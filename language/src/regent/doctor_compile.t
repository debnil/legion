-- Copyright 2018 Stanford University, NVIDIA Corporation
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

-- Legion Doctor

local ast = require("regent/ast")
local ast_util = require("regent/ast_util")
local base = require("regent/std_base")
local data = require("common/data")
local report = require("common/report")
local std = require("regent/std")
local symbol_table = require("regent/symbol_table")
local type_check = require("regent/type_check")

local c = std.c

local context = {}

local function_constraints = {}

function context:__index (field)
  local value = context [field]
  if value ~= nil then
    return value
  end
  error("context as no field '" .. field .. "' (in lookup)", 2)
end

function context:__newindex (field, value)
  error ("context has no field '" .. field .. " (in assignment)", 2)
end

function context.new_global_scope()
  local cx = {
    function_to_conflicts = {},
  }
  return setmetatable(cx, context)
end

function context:new_local_scope()
  local cx = {
    privileges = {},
  }
  setmetatable(cx, context)
  return cx
end

function context:new_task_scope()
  local cx = {
    function_to_conflicts = {},
    region_to_fields = {},
    privilege_to_region = {},
    access_mapping = {},
    privilege_mapping = {},
    created_regions = {},
    constraints = {},
    partitioned_regions = {},
    unpartitioned_regions = {},
  }
  setmetatable(cx, context)
  return cx
end

function context:map_region_fields(region)
  local struct_type = region:gettype():fspace()
  local field_paths, field_types = std.flatten_struct_fields(struct_type)

  if self.region_to_fields == nil then
    self.region_to_fields = {}
  end
  if self.region_to_fields[region] == nil then
    self.region_to_fields[region] = {}
    for i, v in pairs(field_paths) do
      table.insert(self.region_to_fields[region], region:getname() .. "." .. v:mkstring("", ".", ""))
    end
  end
end

function dump(t,indent)
    local names = {}
    if not indent then indent = "" end
    for n,g in pairs(t) do
        table.insert(names,n)
    end
    table.sort(names)
    for i,n in pairs(names) do
        local v = t[n]
        if type(v) == "table" then
            if(v==t) then -- prevent endless loop if table contains reference to itself
                print(indent..tostring(n)..": <-")
            else
                print(indent..tostring(n)..":")
                dump(v,indent.."   ")
            end
        else
            if type(v) == "function" then
                print(indent..tostring(n).."()")
            else
                print(indent..tostring(n)..": "..tostring(v))
            end
        end
    end
end

local function update_privileges(privilege, old_privileges)
  if privilege == "reads" then
    if old_privileges["wo"] ~= nil then
      old_privileges["wo"] = nil
      old_privileges["rw"] = true
    else
      old_privileges["ro"] = true
    end
  elseif privilege == "writes" then
    if old_privileges["ro"] ~= nil then
      old_privileges["ro"] = nil
      old_privileges["rw"] = true
    else
      old_privileges["wo"] = true
    end
  elseif privilege == "reduces +" then
    old_privileges["+"] = true
  elseif privilege == "reduces -" then
    old_privileges["-"] = true
  elseif privilege == "reduces *" then
    old_privileges["*"] = true
  elseif privilege == "reduces /" then
    old_privileges["/"] = true
  elseif privilege == "reduces min" then
    old_privileges["min"] = true
  elseif privilege == "reduces max" then
    old_privileges["max"] = true
  end

  return old_privileges
end

function check_conflicting_overlap(first_field_priv, second_field_priv)
  local conflicting_overlap = false
  for first_field, first_priv in pairs(first_field_priv) do
    for second_field, second_priv in pairs(second_field_priv) do
      if first_field == second_field then
        if first_priv:match("reduces") then
          if first_priv ~= second_priv then
            conflicting_overlap = true
          end

        elseif first_priv ~= "reads" or second_priv ~= "reads" then
          conflicting_overlap = true
        end
      end
    end
  end
  return conflicting_overlap
end

function map_function_to_conflicting(cx, node)
  local privileges_node_table = node.privileges
  local params_node = node.params

  local region_field_privilege = {}

  for _, privileges_node in ipairs(privileges_node_table) do
    for _, priv_node in ipairs(privileges_node) do
      local region = priv_node.region:getname()
      local field_paths, field_types = std.flatten_struct_fields(priv_node.region:gettype():fspace())

      if region_field_privilege[region] == nil then
        region_field_privilege[region] = {}
        
        for idx, field in pairs(field_paths) do
          local field_str = unpack(field)
          if field_str == nil then
            field_str = " "
          end
          region_field_privilege[region][field_str] = " "
        end
      end

      local field_str = unpack(priv_node.field_path)
      local privilege = tostring(priv_node.privilege)
      if field_str == nil then
        for idx, field in pairs(field_paths) do
          local field_str = unpack(field)
          if field_str == nil then
            field_str = " "
          end

          if region_field_privilege[region][field_str] == " " then
            region_field_privilege[region][field_str] = privilege
          else
            region_field_privilege[region][field_str] = "rw"
          end
        end
      end
    end
  end

  local constraint_list = {}
  for i = 1, #params_node do
    if std.is_region(params_node[i].param_type) then
      for j = i+1, #params_node do
        if std.is_region(params_node[j].param_type) then
          local first_region = params_node[i].symbol:getname()
          local second_region = params_node[j].symbol:getname()
          if region_field_privilege[first_region] ~= nil and region_field_privilege[second_region] ~= nil then
            if check_conflicting_overlap(region_field_privilege[first_region], region_field_privilege[second_region]) then
              table.insert(constraint_list, {i, j})
            end
          end
        end
      end
    end
  end

  function_constraints[unpack(node.name)] = constraint_list
end

function context:map_privilege_region(privilege, region, field_path)
  context:map_region_fields(region)
  local privilege = tostring(privilege)
  local region_name = region:getname()
  local key = region_name .. "." .. field_path:mkstring("", ".", "")

  local insert_values = {}
  for _, v in ipairs(context.region_to_fields[region]) do
    if string.find(v, key) ~= nil then
      table.insert(insert_values, v)
    end
  end

  for k, v in ipairs(insert_values) do
    if self.privilege_mapping[v] == nil then
      self.privilege_mapping[v] = {}
    end
    update_privileges(privilege, self.privilege_mapping[v])
  end
end

local function map_access_helper(node)
  if node:is(ast.typed.expr.FieldAccess) then
    return map_access_helper(node.value) .. '.' .. node.field_name
  elseif node:is(ast.typed.expr.Deref) then
    return map_access_helper(node.value)
  elseif node:is(ast.typed.expr.ID) then
    local region_symbol = (node.expr_type.refers_to_type.bounds_symbols)[1]:getname()
    return region_symbol
  elseif node:is(ast.typed.expr.Constant) then
    return nil
  end
end

local function map_write_access(cx, node)
  if not node then return end

  local key_value_string = map_access_helper(node)
  if key_value_string == nil then
    return 
  end

  if cx.access_mapping[key_value_string] == nil then
    cx.access_mapping[key_value_string] = {}
    cx.access_mapping[key_value_string]["wo"] = true
  elseif cx.access_mapping[key_value_string]["ro"] == true then
    cx.access_mapping[key_value_string]["ro"] = nil
    cx.access_mapping[key_value_string]["rw"] = true
  else
    cx.access_mapping[key_value_string]["wo"] = true
  end
end

local function map_reduce_access(cx, node)
  if not node then return end

  local reduce_key = map_access_helper(node.lhs)

  local op = tostring(node.op)
  if cx.access_mapping[reduce_key] == nil then
    cx.access_mapping[reduce_key] = {}
  end
  cx.access_mapping[reduce_key][op] = true
end

local function map_read_access(cx, node)
  if not node then return end

  local key_value_string = map_access_helper(node)
  if key_value_string == nil then
    return
  end
  
  if cx.access_mapping[key_value_string] == nil then
    cx.access_mapping[key_value_string] = {}
    cx.access_mapping[key_value_string]["ro"] = true
  elseif cx.access_mapping[key_value_string]["wo"] == true then
    cx.access_mapping[key_value_string]["wo"] = nil
    cx.access_mapping[key_value_string]["rw"] = true
  else
    cx.access_mapping[key_value_string]["ro"] = true
  end
end

local function find_extra_privileges(cx, node)
  if node:is(ast.privilege.Privilege) then
    cx:map_privilege_region(node.privilege, node.region, node.field_path)
  elseif node:is(ast.typed.stat.Assignment) then
    map_write_access(cx, node.lhs)
    map_read_access(cx, node.rhs)
  elseif node:is(ast.typed.stat.Reduce) then
    map_reduce_access(cx, node)
  end
  -- TODO: Add check for return.
end

local function find_extra_region_creation(cx, node)
  if node:is(ast.typed.stat.Var) then
    if node.value:is(ast.typed.expr.Region) then
      local key = tostring(node.symbol:getname())
      cx.created_regions[key] = true
    end
  elseif node:is(ast.typed.stat.RawDelete) then
    if node.value:is(ast.typed.expr.ID) then
      local key = tostring(node.value.value:getname())
      cx.created_regions[key] = nil
    end
  end
end

local function find_overlapping_regions(cx, node)
  if node:is(ast.typed.expr.Call) then
    local function_name = node.fn.value.name

    if (type(function_name) == "table") then
      function_name = unpack(function_name)
    end

    if function_constraints[function_name] == nil then
      return
    end

    local node_args = node.args
    for i, constraint_pair in pairs(function_constraints[function_name]) do
      local first_idx = constraint_pair[1]
      local second_idx = constraint_pair[2]

      local lhs = std.as_read(node.args[first_idx].expr_type)
      local rhs = std.as_read(node.args[second_idx].expr_type)
      local op = std.disjointness
      
      if std.check_constraint(cx, std.constraint(lhs, rhs, op)) == nil then
        local line_num = tostring(node.span.start.line)
        local warn_msg = "At line " .. line_num .. " arguments " .. tostring(first_idx) .. " and " .. tostring(second_idx) .. " are not disjoint."
        report.warn(node, warn_msg)
      end
    end
  end
end

local function check_privilege_noninterference(cx, task, arg, other_arg, mapping)
  local region_type = std.as_read(arg.expr_type)
  local other_region_type = std.as_read(other_arg.expr_type)
  local param_region_type = mapping[arg]
  local other_param_region_type = mapping[other_arg]

  assert(param_region_type and other_param_region_type)

  local privileges_by_field_path, coherence_modes_by_field_path =
    std.group_task_privileges_by_field_path(
      std.find_task_privileges(param_region_type, task))
  local other_privileges_by_field_path, other_coherence_modes_by_field_path =
    std.group_task_privileges_by_field_path(
      std.find_task_privileges(other_param_region_type, task))

  for field_path, privilege in pairs(privileges_by_field_path) do
    local other_privilege = other_privileges_by_field_path[field_path]

    if not (
        not privilege or privilege == "none" or
        not other_privilege or other_privilege == "none" or
        (privilege == "reads" and other_privilege == "reads") or
        (std.is_reduction_op(privilege) and privilege == other_privilege) or
        (coherence_modes_by_field_path[field_path] == "simultaneous" and
         other_coherence_modes_by_field_path[field_path] == "simultaneous"))
    then
      return false
    end
  end
  return true
end

local function analyze_noninterference_previous(cx, task, arg, regions_previously_used, mapping)
  local region_type = std.as_read(arg.expr_type)
  for i, other_arg in pairs(regions_previously_used) do
    local other_region_type = std.as_read(other_arg.expr_type)
    local constraint = std.constraint(region_type, other_region_type, std.disjointness)

    if std.type_maybe_eq(region_type.fspace_type, other_region_type.fspace_type) and
      not std.check_constraint(cx, constraint) and
      not check_privilege_noninterference(cx, task, arg, other_arg, mapping)
    then
      return false, i
    end
  end
  return true
end

local function find_conflicting_inputs_body(cx, node)
  print('top of find_conflicting_inputs_body')
  local call
  
  if node:is(ast.typed.stat.Expr) and node.expr:is(ast.typed.expr.Call) then
    call = node.expr
  elseif node:is(ast.typed.stat.Reduce) and node.rhs:is(ast.typed.expr.Call) then
    call = node.rhs
    reduce_lhs = node.lhs
    reduce_op = node.op
  elseif node:is(ast.typed.expr.Call) then
    call = node
  elseif node:is(ast.typed.stat.Block) then
    local block_stat = node.block.stats[#node.block.stats]
    if block_stat:is(ast.typed.stat.If) then
      local thenblock_stat = block_stat.then_block.stats[#block_stat.then_block.stats]
      if thenblock_stat:is(ast.typed.stat.Expr) and thenblock_stat.expr:is(ast.typed.expr.Call) then
        call = thenblock_stat.expr
      end
    end
  else
    return
  end

  local task = call.fn.value
  if not std.is_task(task) then
    return -- Not a task
  end

  print('found a call to a task!')
  
  local param_types = task:get_type().parameters
  local args = call.args

  local regions_previously_used = terralib.newlist()
  local mapping = {}
  for i, arg in ipairs(args) do
    mapping[arg] = param_types[i]
    -- arg:printpretty()

    local arg_type = std.as_read(arg.expr_type)
    if std.is_region(arg_type) then
      local passed, failure_i = analyze_noninterference_previous(cx, task, arg, regions_previously_used, mapping)
      if not passed then
        report_fail(node, "Conflicting arguments " .. tostring(i) " and " .. tostring(failure_i))
      end
      regions_previously_used[i] = arg
    end
  end
end

local function find_conflicting_inputs_loop(cx, node)
  if node:is(ast.typed.stat.ForNum) or node:is(ast.typed.stat.ForList) then
    if #node.block.stats > 0 then
      local body = node.block.stats[#node.block.stats]
      find_conflicting_inputs_body(cx, body)
    end
  elseif node:is(ast.typed.stat.IndexLaunchNum) then
    find_conflicting_inputs_body(cx, node.call)
  end
end

function print_extra_privileges(cx, node)
  local extra_privileges = {}
  for field, curr_privileges in pairs(cx.privilege_mapping) do
    if cx.access_mapping[field] ~= nil then
      for access, _ in pairs(cx.access_mapping[field]) do
        curr_privileges[access] = nil
      end
    end
    
    local num_priv_after_removal = 0
    for k, v in pairs(curr_privileges) do
      num_priv_after_removal = num_priv_after_removal + 1
    end
    if num_priv_after_removal > 0 then
      if curr_privileges["rw"] == nil then
        extra_privileges[field] = true
      end
    end
  end

  local num_extra_privileges = 0
  for k, v in pairs(extra_privileges) do
    num_extra_privileges = num_extra_privileges + 1
  end
  if num_extra_privileges > 0 then
    print("The following fields have extra_privileges: ")
    for k, v in pairs(extra_privileges) do 
      print(k)
    end
  end
end

function print_extra_creation(cx, node)
  local num_extra_creations = 0
  for field, _ in pairs(cx.created_regions) do
    num_extra_creations = num_extra_creations + 1
  end
  if num_extra_creations > 0 then
    print("The following created regions are not deleted: ")
    for field, _ in pairs(cx.created_regions) do
      print(field)
    end
  end
end

local function find_region_partitions(cx, node)
  if node:is(ast.typed.stat.Var) then
    if node.value:is(ast.typed.expr.Region) then
      local key = node.symbol:gettype()
      cx.unpartitioned_regions[key] = true
    elseif node.value:is(ast.typed.expr.Partition) then
      local key = std.as_read(node.value.region.expr_type)
      cx.unpartitioned_regions[key] = nil
      cx.partitioned_regions[key] = true
    end
  end

  if node:is(ast.typed.expr.Call) then
    for _, arg in ipairs(node.args) do
      if std.is_rawref(arg.expr_type) then
        local region_name = std.as_read(arg.expr_type)

        -- TODO properly format warning message.
        if cx.partitioned_regions[region_name] ~= nil then
          local line_num = tostring(node.span.start.line)
          local warn_msg = 'At line ' .. line_num .. ', ran task using region instead of partitioned version.'
          report.warn(node, warn_msg)
        end
      end
    end
  end

end

local doctor_compile = {}

local function doctor_compile_node(cx)
  return function(node)
    find_extra_privileges(cx, node)
    -- find_extra_region_creation(cx, node)
    find_overlapping_regions(cx, node)
    find_region_partitions(cx, node)
    find_conflicting_inputs_loop(cx, node)

    return node
  end
end 

function doctor_compile.block(cx, node)
  return ast.map_node_postorder(doctor_compile_node(cx), node)
  -- return ast.flatmap_node_postorder(doctor_compile_node(cx), node)
end

function doctor_compile.top_task(cx, node)
  if not node.body then return node end
  local cx = cx:new_task_scope()
  cx.constraints = node.prototype:get_constraints()
  local body = doctor_compile.block(cx, node.body)

  print_extra_privileges(cx, node)
  -- print_extra_creation(cx, node)
  return node {body = body}
end

function doctor_compile.top(cx, node)
  if node:is(ast.typed.top.Task) then
    print(unpack(node.name))
    map_function_to_conflicting(cx, node)
    return doctor_compile.top_task(cx, node)
  else
    return node
  end
end

function doctor_compile.entry(node)
  local cx = context.new_global_scope({})
  return doctor_compile.top(cx, node)
end

doctor_compile.pass_name = "doctor-compile"

return doctor_compile
