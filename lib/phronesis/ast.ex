# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.AST do
  @moduledoc """
  Abstract Syntax Tree node definitions for Phronesis.

  The AST follows the grammar specification with these node types:

  ## Top-Level Declarations

  - `{:policy, name, condition, action, metadata}` - Policy declaration
  - `{:import, module_path, alias}` - Import statement
  - `{:const, name, expression}` - Constant declaration

  ## Expressions

  - `{:binary_op, op, left, right}` - Binary operations (+, -, *, /, AND, OR)
  - `{:unary_op, op, operand}` - Unary operations (NOT, -)
  - `{:comparison, op, left, right}` - Comparisons (==, !=, >, <, etc.)
  - `{:module_call, path, args}` - Module function call
  - `{:identifier, name}` - Variable reference
  - `{:literal, type, value}` - Literal values

  ## Actions

  - `{:execute, function, args}` - Execute action
  - `{:report, message}` - Report action
  - `{:reject, reason}` - Reject action
  - `{:accept, reason}` - Accept action
  - `{:block, actions}` - Compound action (BEGIN...END)
  - `{:conditional, condition, then_action, else_action}` - IF/THEN/ELSE

  ## Metadata

  - `%{priority: int, expires: :never | datetime, created_by: identifier}`
  """

  @type name :: String.t()
  @type module_path :: [name()]

  @type literal_type :: :integer | :float | :string | :boolean | :ip_address | :datetime
  @type literal :: {:literal, literal_type(), any()}

  @type comparison_op :: :eq | :neq | :gt | :gte | :lt | :lte | :in
  @type binary_op :: :add | :sub | :mul | :div | :and | :or
  @type unary_op :: :not | :neg

  @type expression ::
          {:binary_op, binary_op(), expression(), expression()}
          | {:unary_op, unary_op(), expression()}
          | {:comparison, comparison_op(), expression(), expression()}
          | {:module_call, module_path(), [expression()]}
          | {:identifier, name()}
          | literal()

  @type action ::
          {:execute, name(), [expression()]}
          | {:report, expression()}
          | {:reject, expression() | nil}
          | {:accept, expression() | nil}
          | {:block, [action()]}
          | {:conditional, expression(), action(), action() | nil}

  @type metadata :: %{
          priority: non_neg_integer(),
          expires: :never | String.t(),
          created_by: name() | nil
        }

  @type policy :: {:policy, name(), expression(), action(), metadata()}
  @type import_decl :: {:import, module_path(), name() | nil}
  @type const_decl :: {:const, name(), expression()}

  @type declaration :: policy() | import_decl() | const_decl()
  @type program :: [declaration()]

  @doc """
  Create a policy node.
  """
  @spec policy(name(), expression(), action(), metadata()) :: policy()
  def policy(name, condition, action, metadata) do
    {:policy, name, condition, action, metadata}
  end

  @doc """
  Create an import node.
  """
  @spec import_decl(module_path(), name() | nil) :: import_decl()
  def import_decl(path, alias_name \\ nil) do
    {:import, path, alias_name}
  end

  @doc """
  Create a constant declaration node.
  """
  @spec const_decl(name(), expression()) :: const_decl()
  def const_decl(name, value) do
    {:const, name, value}
  end

  @doc """
  Create a binary operation node.
  """
  @spec binary_op(binary_op(), expression(), expression()) :: expression()
  def binary_op(op, left, right) do
    {:binary_op, op, left, right}
  end

  @doc """
  Create a comparison node.
  """
  @spec comparison(comparison_op(), expression(), expression()) :: expression()
  def comparison(op, left, right) do
    {:comparison, op, left, right}
  end

  @doc """
  Create a unary operation node.
  """
  @spec unary_op(unary_op(), expression()) :: expression()
  def unary_op(op, operand) do
    {:unary_op, op, operand}
  end

  @doc """
  Create a module call node.
  """
  @spec module_call(module_path(), [expression()]) :: expression()
  def module_call(path, args) do
    {:module_call, path, args}
  end

  @doc """
  Create an identifier node.
  """
  @spec identifier(name()) :: expression()
  def identifier(name) do
    {:identifier, name}
  end

  @doc """
  Create a literal node.
  """
  @spec literal(literal_type(), any()) :: literal()
  def literal(type, value) do
    {:literal, type, value}
  end

  @doc """
  Create an interpolated string node (v0.2.x).

  Parts is a list of either:
  - `{:string, "literal text"}`
  - `{:expr, [tokens]}`
  """
  @spec interpolated_string([{:string, String.t()} | {:expr, list()}]) :: expression()
  def interpolated_string(parts) do
    {:interpolated_string, parts}
  end

  @doc """
  Create a field access node (record.field).
  """
  @spec field_access(expression(), name()) :: expression()
  def field_access(base, field) do
    {:field_access, base, field}
  end

  @doc """
  Create an optional access node (v0.2.x: record?.field).

  Returns null if base is null, otherwise accesses the field.
  """
  @spec optional_access(expression(), name()) :: expression()
  def optional_access(base, field) do
    {:optional_access, base, field}
  end

  @doc """
  Create an execute action node.
  """
  @spec execute(name(), [expression()]) :: action()
  def execute(function, args \\ []) do
    {:execute, function, args}
  end

  @doc """
  Create a report action node.
  """
  @spec report(expression()) :: action()
  def report(message) do
    {:report, message}
  end

  @doc """
  Create a reject action node.
  """
  @spec reject(expression() | nil) :: action()
  def reject(reason \\ nil) do
    {:reject, reason}
  end

  @doc """
  Create an accept action node.
  """
  @spec accept(expression() | nil) :: action()
  def accept(reason \\ nil) do
    {:accept, reason}
  end

  @doc """
  Create a block action node.
  """
  @spec block([action()]) :: action()
  def block(actions) do
    {:block, actions}
  end

  @doc """
  Create a conditional action node.
  """
  @spec conditional(expression(), action(), action() | nil) :: action()
  def conditional(condition, then_action, else_action \\ nil) do
    {:conditional, condition, then_action, else_action}
  end

  @doc """
  Create policy metadata.
  """
  @spec metadata(keyword()) :: metadata()
  def metadata(opts \\ []) do
    %{
      priority: Keyword.get(opts, :priority, 0),
      expires: Keyword.get(opts, :expires, :never),
      created_by: Keyword.get(opts, :created_by)
    }
  end
end
