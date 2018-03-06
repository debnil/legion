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
local data = require("common/data")
local report = require("common/report")
local std = require("regent/std")
local type_check = require("regent/type_check")

local context = {}

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
  local cx = {}
  return setmetatable(cx, context)
end

function context:new_local_scope()
  local cx = {
    privileges = {},
  }
  return setmetatable(cx, context)
end

function context:new_task_scope()
  local cx = {
    region_to_fspace = {},
    region_to_fields = {},
    privilege_to_region = {},
    write_access = {},
    read_access = {},
    reduce_access = {},
    reduce_plus_access = {},
    reduce_minus_access = {},
    reduce_multiply_access = {},
    reduce_divide_access = {},
    reduce_min_access = {},
    reduce_max_access = {},
  }
  return setmetatable(cx, context)
end

function context:map_region_fspace(region, fspace)
  self.region_to_fspace[region:getname()] = tostring(fspace)
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

function context:map_privilege_region(privilege, region, field_path)
  context:map_region_fields(region)
  local privilege = tostring(privilege)
  local key = region:getname()
  
  if self.privilege_to_region[privilege] == nil then
    self.privilege_to_region[privilege] = {}
  end
  -- if self.privilege_to_region[privilege][key] == nil then
  -- self.privilege_to_region[privilege][key] = {}
  -- end

  local insert_values = {}
  local privilege_value = key .. "." .. field_path:mkstring("", ".", "")
  for _, v in ipairs(context.region_to_fields[region]) do
    if string.find(v, privilege_value) ~= nil then
      table.insert(insert_values, v)
    end
  end

  for k, v in ipairs(insert_values) do
    -- table.insert(self.privilege_to_region[privilege][key], v)
    self.privilege_to_region[privilege][v] = true
  end
end

-- TODO: Change string concat to tuple using data.newtuple.
-- NB: Tuple just array of objects, mkstring (better for consistency)
function map_access_helper(node)
  if node:is(ast.typed.expr.FieldAccess) then
    return map_access_helper(node.value) .. '.' .. node.field_name
  elseif node:is(ast.typed.expr.Deref) then
    return map_access_helper(node.value)
  elseif node:is(ast.typed.expr.ID) then
    -- node:printpretty()
    -- return node.value:getname()
    local region_symbol_table = node.expr_type.refers_to_type.bounds_symbols
    local region_symbol = region_symbol_table[1]:getname()
    return region_symbol
  elseif node:is(ast.typed.expr.Constant) then
    return nil
  else
    print('why did it go here')
  end
end

function map_write_access(cx, node)
  if not node then return end
  local key_value_string = map_access_helper(node)
  if key_value_string ~= nil then
    -- NB: Work with tuple here
    cx.write_access[key_value_string] = true
    -- table.insert(cx.write_access, key_value_string)
  end
end

function map_read_access(cx, node)
  if not node then return end
  -- print('calling map read access')
  local key_value_string = map_access_helper(node)
  -- print(key_value_string)
  if key_value_string ~= nil then
    table.insert(cx.read_access, key_value_string)
  end
end

function find_extra_writes(cx) 
  local extra_writes = {}
  if cx.privilege_to_region["writes"] == nil then return nil end
  for write_key, _ in pairs(cx.privilege_to_region["writes"]) do
    if cx.write_access[write_key] == nil then
      extra_writes[write_key] = true
    end
  end
  return extra_writes
end

function find_extra_reads(cx) 
  local extra_reads = {}
  if cx.privilege_to_region["reads"] == nil then return nil end
  for read_key, _ in pairs(cx.privilege_to_region["reads"]) do
    if cx.read_access[read_key] == nil then
      extra_reads[read_key] = true
    end
  end
  return extra_reads
end

function find_extra_reduces(cx)
  local extra_reduces = {}
  if cx.privilege_to_region["reduces +"] ~= nil then
    for reduce_key, _ in pairs(cx.privilege_to_region["reduces +"]) do
      if cx.reduce_plus_access[reduce_key] == nil and (cx.read_access[reduce_key] == nil and cx.write_access[reduce_key] == nil) then
        extra_reduces[reduce_key] = true
      end
    end
  end
  if cx.privilege_to_region["reduces -"] ~= nil then
    for reduce_key, _ in pairs(cx.privilege_to_region["reduces -"]) do
      if cx.reduce_minus_access[reduce_key] == nil and (cx.read_access[reduce_key] == nil and cx.write_access[reduce_key] == nil) then
        extra_reduces[reduce_key] = true
      end
    end
  end
  if cx.privilege_to_region["reduces *"] ~= nil then
    for reduce_key, _ in pairs(cx.privilege_to_region["reduces *"]) do
      if cx.reduce_multiply_access[reduce_key] == nil and (cx.read_access[reduce_key] == nil and cx.write_access[reduce_key] == nil) then
        extra_reduces[reduce_key] = true
      end
    end
  end
  if cx.privilege_to_region["reduces /"] ~= nil then
    for reduce_key, _ in pairs(cx.privilege_to_region["reduces /"]) do
      if cx.reduce_divide_access[reduce_key] == nil and (cx.read_access[reduce_key] == nil and cx.write_access[reduce_key] == nil) then
        extra_reduces[reduce_key] = true
      end
    end
  end
  if cx.privilege_to_region["reduces min"] ~= nil then
    for reduce_key, _ in pairs(cx.privilege_to_region["reduces min"]) do
      if cx.reduce_min_access[reduce_key] == nil and (cx.read_access[reduce_key] == nil and cx.write_access[reduce_key] == nil) then
        extra_reduces[reduce_key] = true
      end
    end
  end
  if cx.privilege_to_region["reduces max"] ~= nil then
    for reduce_key, _ in pairs(cx.privilege_to_region["reduces max"]) do
      if cx.reduce_max_access[reduce_key] == nil and (cx.read_access[reduce_key] == nil and cx.write_access[reduce_key] == nil) then
        extra_reduces[reduce_key] = true
      end
    end
  end
  if #extra_reduces == 0 then 
    return nil
  end
  return extra_reduces
end

function map_reduce_access(cx, node)
  if not node then return end
  local reduce_key = map_access_helper(node.lhs)
  if node.op == "+" then
    if cx.reduce_plus_access[reduce_key] == nil then
      cx.reduce_plus_access[reduce_key] = true
    end
  elseif node.op == "-" then
    if cx.reduce_minus_access[reduce_key] == nil then
      cx.reduce_minus_access[reduce_key] = true
    end
  elseif node.op == "*" then
    if cx.reduce_multiply_access[reduce_key] == nil then
      cx.reduce_multiply_access[reduce_key] = true
    end
  elseif node.op == "/" then
    if cx.reduce_divide_access[reduce_key] == nil then
      cx.reduce_divide_access[reduce_key] = true
    end
  elseif node.op == "min" then
    if cx.reduce_min_access[reduce_key] == nil then
      cx.reduce_min_access[reduce_key] = true
    end
  elseif node.op == "max" then
    if cx.reduce_max_access[reduce_key] == nil then
      cx.reduce_max_access[reduce_key] = true
    end    
  end
end

local function reconcile_readwrite_reduce(cx, extra_writes, extra_reads)
  if extra_writes == nil and extra_reads == nil then return extra_writes, extra_reads end
  for reduce_key, _ in pairs(cx.reduce_plus_access) do
    if extra_writes[reduce_key] ~= nil and extra_reads[reduce_key] ~= nil then
      -- print(reduce_key)
      extra_writes[reduce_key] = nil
      extra_reads[reduce_key] = nil
    end
  end
  for reduce_key, _ in pairs(cx.reduce_minus_access) do
    if extra_writes[reduce_key] ~= nil and extra_reads[reduce_key] ~= nil then
      print(reduce_key)
      extra_writes[reduce_key] = nil
      extra_reads[reduce_key] = nil
    end
  end
  for reduce_key, _ in pairs(cx.reduce_multiply_access) do
    if extra_writes[reduce_key] ~= nil and extra_reads[reduce_key] ~= nil then
      print(reduce_key)
      extra_writes[reduce_key] = nil
      extra_reads[reduce_key] = nil
    end
  end
  for reduce_key, _ in pairs(cx.reduce_divide_access) do
    if extra_writes[reduce_key] ~= nil and extra_reads[reduce_key] ~= nil then
      print(reduce_key)
      extra_writes[reduce_key] = nil
      extra_reads[reduce_key] = nil
    end
  end
  for reduce_key, _ in pairs(cx.reduce_min_access) do
    if extra_writes[reduce_key] ~= nil and extra_reads[reduce_key] ~= nil then
      print(reduce_key)
      extra_writes[reduce_key] = nil
      extra_reads[reduce_key] = nil
    end
  end
  for reduce_key, _ in pairs(cx.reduce_max_access) do
    if extra_writes[reduce_key] ~= nil and extra_reads[reduce_key] ~= nil then
      print(reduce_key)
      extra_writes[reduce_key] = nil
      extra_reads[reduce_key] = nil
    end
  end
  return extra_writes, extra_reads
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

local function find_extra_privileges(cx, node)
  if node:is(ast.typed.top.TaskParam) then
    cx:map_region_fspace(node.symbol, node.param_type)
    -- dump(cx.region_to_fspace)
  elseif node:is(ast.privilege.Privilege) then
    cx:map_privilege_region(node.privilege, node.region, node.field_path)
    -- dump(cx.privilege_to_region)
  elseif node:is(ast.typed.stat.Assignment) then
    -- TODO: Add logic for checking sign. 
    map_write_access(cx, node.lhs)
    map_read_access(cx, node.rhs)
  elseif node:is(ast.typed.stat.Reduce) then
    map_reduce_access(cx, node)
  end
  -- TODO: Add check for return.
end

local function print_extra_privileges(cx, node)
  local extra_writes = find_extra_writes(cx)
  local extra_reads = find_extra_reads(cx)
  extra_writes, extra_reads = reconcile_readwrite_reduce(cx, extra_writes, extra_reads)

  if extra_writes ~= nil then
    print(tostring(node.name) .. ' has the following extra write privileges:')
    for k, _ in pairs(extra_writes) do print(k) end
  end

  if extra_reads ~= nil then
    print(tostring(node.name) .. ' has the following extra read privileges:')
    for k, _ in pairs(extra_reads) do print(k) end
  end

  local extra_reduces = find_extra_reduces(cx)
  if extra_reduces ~= nil then
    print(tostring(node.name) .. ' has the following extra reduce privileges:')
    for k, _ in pairs(extra_reduces) do print(k) end
  end
end

local doctor = {}

local function doctor_node(cx)
  return function(node)
    -- node:printpretty()
    find_extra_privileges(cx, node)
  end
end 

function doctor.block(cx, node)
  return ast.traverse_node_postorder(doctor_node(cx), node)
end

function doctor.top_task(cx, node)
  if not node.body then return node end
  -- print(node.name)
  local cx = cx:new_task_scope()
  doctor.block(cx, node)

  print_extra_privileges(cx, node)
  return node
end

function doctor.top(cx, node)
  if node:is(ast.typed.top.Task) then
    return doctor.top_task(cx, node)
  else
    return node
  end
end

function doctor.entry(node)
  local cx = context.new_global_scope({})
  return doctor.top(cx, node)
end

doctor.pass_name = "doctor"

return doctor
