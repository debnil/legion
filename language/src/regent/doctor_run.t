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

local doctor_run = {}

-- Check that all region sizes are less than some threshold.
function doctor_run.stat_expr(cx, node)
  local call = node.expr

  if not call:is(ast.typed.expr.Call) then
    return node -- Not a call
  end

  if not std.is_task(call.fn.value) then
    return node -- Not a call to a task
  end

  if #data.filter(
    function(arg) return std.is_region(std.as_read(arg.expr_type)) end,
    call.args) == 0
  then
    return node -- Task call has no region arguments
  end

  local conditions = terralib.newlist()
  local result_stats = terralib.newlist()
  local result_args = terralib.newlist()
  for _, arg in ipairs(call.args) do
    local arg_type = std.as_read(arg.expr_type)

    if not std.is_region(arg_type) then
      result_args:insert(arg)
    else
      local arg_symbol = std.newsymbol(arg_type)
      local arg_var = ast.typed.stat.Var {
        symbol = arg_symbol,
        type = arg_type,
        value = arg,
        annotations = ast.default_annotations(),
        span = arg.span,
      }
      local arg_ref = ast.typed.expr.ID {
        value = arg_symbol,
        expr_type = std.rawref(&arg_type),
        annotations = ast.default_annotations(),
        span = arg.span,
      }
      local condition = ast.typed.expr.Binary {
        op = "<",
        lhs = ast.typed.expr.FieldAccess {
          value = ast.typed.expr.FieldAccess {
            value = arg_ref,
            field_name = "ispace",
            expr_type = arg_type:ispace(),
            annotations = ast.default_annotations(),
            span = arg.span,
          },
          field_name = "volume",
          expr_type = int64,
          annotations = ast.default_annotations(),
          span = arg.span,
        },
        -- TODO make value below variable
        rhs = ast.typed.expr.Constant {
          value = 100000,
          expr_type = int64,
          annotations = ast.default_annotations(),
          span = arg.span,
        },
        expr_type = bool,
        annotations = ast.default_annotations(),
        span = arg.span,
      }

      result_stats:insert(arg_var)
      result_args:insert(arg_ref)
      conditions:insert(condition)
    end
  end

  local skip_condition = data.reduce(
    function(expr, condition)
      return ast.typed.expr.Binary {
        op = "or",
        lhs = expr,
        rhs = condition,
        expr_type = bool,
        annotations = ast.default_annotations(),
        span = call.span,
      }
    end,
    conditions)

  -- TODO modify region warning statement to make clearer
  local print_expr = ast_util.mk_expr_call(c.printf, ast_util.mk_expr_constant("Region size exceeds threshold value.\n", rawstring))
  local maybe_call = ast.typed.stat.If {
    cond = skip_condition,
    then_block = ast.typed.Block {
      stats = terralib.newlist({ node { expr = call { args = result_args } } }),
      span = call.span,
    },
    elseif_blocks = terralib.newlist(),
    else_block = ast.typed.Block {
      stats = terralib.newlist({
        ast_util.mk_stat_expr(print_expr)
      }),
      span = call.span,
    },
    annotations = ast.default_annotations(),
    span = call.span,
  }

  result_stats:insert(maybe_call)
  
  return ast.typed.stat.Block {
    block = ast.typed.Block {
      stats = result_stats,
      span = call.span,
    },
    annotations = ast.default_annotations(),
    span = call.span,
  }
end

function doctor_run.stat_var(cx, node)
  if not (node.value:is(ast.typed.expr.Partition) or node.value:is(ast.typed.expr.PartitionEqual)) then
    return node -- Not a Partition
  end

  local result_list = terralib.newlist()
  result_list:insert(node)

  local loop_stats = terralib.newlist()

  local index_symbol = std.newsymbol(int32)
  
  local node_type = std.as_read(node.value.expr_type)
  local ispace_type = std.as_read(node.value.colors.expr_type)

  -- partition[i].ispace.volume / 
  local loop_if_cond_lhs = ast.typed.expr.Binary {
    op = "/",
    span = node.span,
    annotations = ast.default_annotations(),
    expr_type = int64,
    rhs = ast.typed.expr.FieldAccess {
      span = node.span,
      annotations = ast.default_annotations(),
      expr_type = int64,
      field_name = "volume",
      value = ast.typed.expr.FieldAccess {
        span = node.span,
        annotations = ast.default_annotations(),
        expr_type = ispace_type, -- TODO fill ispace(ptr),
        field_name = "ispace",
        value = ast.typed.expr.IndexAccess {
          span = node.span,
          annotations = ast.default_annotations(),
          expr_type = std.as_read(node.value.region.expr_type),
          value = ast.typed.expr.ID {
            span = node.span,
            annotations = ast.default_annotations(),
            expr_type = std.as_read(node.value.expr_type),
            value = node.symbol,
          }, 
          index = ast.typed.expr.Cast {
            span = node.span,
            annotations = ast.default_annotations(),
            expr_type = int1d,
            fn = ast.typed.expr.Function {
              span = node.span,
              annotations = ast.default_annotations(),
              expr_type = int1d,
              value = int1d,
            },
            arg = ast.typed.expr.ID {
              span = node.span,
              annotations = ast.default_annotations(),
              expr_type = int32,
              value = index_symbol,
            }
          }
        },
      }
    },
    lhs = ast.typed.expr.FieldAccess {
      span = node.span,
      annotations = ast.default_annotations(),
      expr_type = int64,
      field_name = "volume",
      value = ast.typed.expr.FieldAccess {
        span = node.span,
        annotations = ast.default_annotations(),
        expr_type = ispace(ptr),
        field_name = "ispace",
        value = ast.typed.expr.ID {
          span = node.span,
          annotations = ast.default_annotations(),
          expr_type = std.as_read(node.value.region.expr_type),
          value = node.value.region.value,
        },
      },
    },
  }

  local loop_if_cond = ast.typed.expr.Binary {
    span = node.span,
    annotations = ast.default_annotations(),
    expr_type = bool,
    op = "<",
    rhs = ast.typed.expr.Constant {
      span = node.span,
      expr_type = double,
      value = 10,
      annotations = ast.default_annotations(),
    },
    lhs = loop_if_cond_lhs
  }

  local then_block_stats = terralib.newlist()
  local print_expr = ast_util.mk_expr_call(c.printf, ast_util.mk_expr_constant("A partition is too large\n", rawstring))
  then_block_stats:insert(ast_util.mk_stat_expr(print_expr))

  local loop_if = ast_util.mk_stat_if(loop_if_cond, then_block_stats)

  loop_stats:insert(loop_if)

  local loop_values = terralib.newlist()
  local loop_values_first = ast.typed.expr.Constant {
    span = node.span,
    expr_type = int32,
    value = 0,
    annotations = ast.default_annotations(),
  }

  local loop_values_last = ast.typed.expr.FieldAccess {
    span = node.span,
    annotations = ast.default_annotations(),
    expr_type = int64,
    value = ast.typed.expr.FieldAccess {
      value = ast.typed.expr.ID {
        value = node.symbol,
        expr_type = node_type,
        annotations = ast.default_annotations(),
        span = node.span,
      },
      field_name = "colors",
      expr_type = ispace_type,
      annotations = ast.default_annotations(),
      span = node.span,
    },
    field_name = "volume",
    expr_type = int64,
    annotations = ast.default_annotations(),
    span = node.span,
  }

  loop_values:insert(loop_values_first)
  loop_values:insert(loop_values_last)

  local loop_node = ast.typed.stat.ForNum {
    symbol = index_symbol,
    annotations = ast.default_annotations(),
    span = node.span,
    block = ast.typed.Block {
      span = node.span,
      stats = loop_stats,
    },
    values = loop_values,
  }

  result_list:insert(loop_node)

  return result_list
end

local function doctor_run_node(cx)
  return function(node)
    if node:is(ast.typed.stat.Expr) then
      return doctor_run.stat_expr(cx, node)
    elseif node:is(ast.typed.stat.Var) then
      return doctor_run.stat_var(cx, node)
    end
    return node
  end
end 

function doctor_run.block(cx, node)
  return ast.flatmap_node_postorder(doctor_run_node(cx), node)
end

function doctor_run.top_task(cx, node)
  if not node.body then return node end
  local cx = cx:new_task_scope()
  cx.constraints = node.prototype:get_constraints()
  local body = doctor_run.block(cx, node.body)

  return node {body = body}
end

function doctor_run.top(cx, node)
  if node:is(ast.typed.top.Task) then
    map_function_to_conflicting(cx, node)
    return doctor_run.top_task(cx, node)
  else
    return node
  end
end

function doctor_run.entry(node)
  local cx = context.new_global_scope({})
  return doctor_run.top(cx, node)
end

doctor_run.pass_name = "doctor-run"

return doctor_run