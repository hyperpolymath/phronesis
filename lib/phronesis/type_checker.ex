# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.TypeChecker do
  @moduledoc """
  Static type checker for Phronesis policy programs.

  Phronesis has a simple, decidable type system:

  - Policies return `Action` (Accept | Reject | Report | Execute)
  - IF conditions must be `boolean`
  - AND/OR combine `boolean` operands
  - NOT negates a `boolean`
  - Constants have declared types inferred from their literal values
  - Imports bring external policies into scope
  - Priority metadata must be `integer`
  - Arithmetic operators require numeric operands
  - Comparison operators require matching operand types, produce `boolean`

  ## Usage

      {:ok, tokens} = Phronesis.Lexer.tokenize(source)
      {:ok, ast} = Phronesis.Parser.parse(tokens)
      case Phronesis.TypeChecker.check(ast) do
        :ok -> IO.puts("Type check passed")
        {:error, errors} -> Enum.each(errors, &IO.puts/1)
      end
  """

  # ------------------------------------------------------------------
  # Public API
  # ------------------------------------------------------------------

  @type phronesis_type ::
          :integer
          | :float
          | :string
          | :boolean
          | :ip_address
          | :datetime
          | :action
          | :any

  @type type_error :: %{
          message: String.t(),
          node: any()
        }

  @doc """
  Type-check a complete Phronesis program (list of declarations).

  Returns `:ok` on success or `{:error, [type_error]}` on failure.
  """
  @spec check([any()]) :: :ok | {:error, [type_error()]}
  def check(declarations) when is_list(declarations) do
    # Build the initial scope from constants and imports.
    scope = build_scope(declarations)

    errors =
      declarations
      |> Enum.flat_map(fn decl -> check_declaration(decl, scope) end)

    case errors do
      [] -> :ok
      _ -> {:error, errors}
    end
  end

  # ------------------------------------------------------------------
  # Scope Construction
  # ------------------------------------------------------------------

  defp build_scope(declarations) do
    Enum.reduce(declarations, %{}, fn decl, scope ->
      case decl do
        {:const, name, expr} ->
          Map.put(scope, to_string(name), infer_expr_type(expr, scope))

        {:import, path, alias_name} ->
          key = alias_name || List.last(path) || Enum.join(path, ".")
          Map.put(scope, to_string(key), :any)

        {:policy, _name, _cond, _action, _meta} ->
          scope
      end
    end)
  end

  # ------------------------------------------------------------------
  # Declaration Checking
  # ------------------------------------------------------------------

  defp check_declaration({:policy, name, condition, action, metadata}, scope) do
    cond_errors = check_condition(condition, scope, "policy '#{name}' condition")
    action_errors = check_action(action, scope, "policy '#{name}' action")
    meta_errors = check_metadata(metadata, name)
    cond_errors ++ action_errors ++ meta_errors
  end

  defp check_declaration({:const, name, expr}, scope) do
    # Constants are well-typed if their expression is well-typed.
    case infer_expr_type(expr, scope) do
      :error ->
        [%{message: "Constant '#{name}' has an ill-typed value", node: expr}]

      _ ->
        []
    end
  end

  defp check_declaration({:import, _path, _alias}, _scope) do
    # Imports are assumed correct at the type level.
    []
  end

  defp check_declaration(_other, _scope), do: []

  # ------------------------------------------------------------------
  # Condition Checking (must produce boolean)
  # ------------------------------------------------------------------

  defp check_condition(condition, scope, context) do
    ty = infer_expr_type(condition, scope)

    cond do
      ty == :boolean ->
        []

      ty == :any ->
        # Unresolved; allow conservatively.
        []

      true ->
        [
          %{
            message:
              "#{context}: expected boolean condition, got #{inspect(ty)}",
            node: condition
          }
        ]
    end
  end

  # ------------------------------------------------------------------
  # Action Checking
  # ------------------------------------------------------------------

  defp check_action({:accept, _reason}, _scope, _ctx), do: []
  defp check_action({:reject, _reason}, _scope, _ctx), do: []

  defp check_action({:report, message_expr}, scope, ctx) do
    ty = infer_expr_type(message_expr, scope)

    if ty in [:string, :any] do
      []
    else
      [%{message: "#{ctx}: REPORT message should be a string, got #{inspect(ty)}", node: message_expr}]
    end
  end

  defp check_action({:execute, _function, args}, scope, ctx) do
    # Check each argument is well-typed.
    args
    |> Enum.with_index()
    |> Enum.flat_map(fn {arg, idx} ->
      case infer_expr_type(arg, scope) do
        :error ->
          [%{message: "#{ctx}: EXECUTE argument #{idx + 1} is ill-typed", node: arg}]

        _ ->
          []
      end
    end)
  end

  defp check_action({:block, actions}, scope, ctx) do
    actions
    |> Enum.with_index()
    |> Enum.flat_map(fn {action, idx} ->
      check_action(action, scope, "#{ctx} block statement #{idx + 1}")
    end)
  end

  defp check_action({:conditional, condition, then_action, else_action}, scope, ctx) do
    cond_errors = check_condition(condition, scope, "#{ctx} IF condition")
    then_errors = check_action(then_action, scope, "#{ctx} THEN branch")

    else_errors =
      if else_action do
        check_action(else_action, scope, "#{ctx} ELSE branch")
      else
        []
      end

    cond_errors ++ then_errors ++ else_errors
  end

  defp check_action(_other, _scope, _ctx), do: []

  # ------------------------------------------------------------------
  # Metadata Checking
  # ------------------------------------------------------------------

  defp check_metadata(metadata, policy_name) when is_map(metadata) do
    priority_errors =
      case Map.get(metadata, :priority) do
        nil ->
          []

        p when is_integer(p) and p >= 0 ->
          []

        p when is_integer(p) ->
          [
            %{
              message:
                "Policy '#{policy_name}': priority must be a non-negative integer, got #{p}",
              node: {:priority, p}
            }
          ]

        other ->
          [
            %{
              message:
                "Policy '#{policy_name}': priority must be an integer, got #{inspect(other)}",
              node: {:priority, other}
            }
          ]
      end

    expires_errors =
      case Map.get(metadata, :expires) do
        :never -> []
        nil -> []
        s when is_binary(s) -> []
        other ->
          [
            %{
              message:
                "Policy '#{policy_name}': expires must be :never or a datetime string, got #{inspect(other)}",
              node: {:expires, other}
            }
          ]
      end

    priority_errors ++ expires_errors
  end

  defp check_metadata(_meta, _name), do: []

  # ------------------------------------------------------------------
  # Expression Type Inference
  # ------------------------------------------------------------------

  @doc """
  Infer the type of an expression within the given scope.

  Returns a `phronesis_type` atom or `:error` for ill-typed expressions.
  """
  @spec infer_expr_type(any(), map()) :: phronesis_type() | :error
  def infer_expr_type(expr, scope \\ %{})

  # Literals
  def infer_expr_type({:literal, :integer, _}, _scope), do: :integer
  def infer_expr_type({:literal, :float, _}, _scope), do: :float
  def infer_expr_type({:literal, :string, _}, _scope), do: :string
  def infer_expr_type({:literal, :boolean, _}, _scope), do: :boolean
  def infer_expr_type({:literal, :ip_address, _}, _scope), do: :ip_address
  def infer_expr_type({:literal, :datetime, _}, _scope), do: :datetime

  # Identifiers
  def infer_expr_type({:identifier, name}, scope) do
    Map.get(scope, to_string(name), :any)
  end

  # Binary operations: AND, OR
  def infer_expr_type({:binary_op, op, left, right}, scope)
      when op in [:and, :or] do
    lt = infer_expr_type(left, scope)
    rt = infer_expr_type(right, scope)

    cond do
      lt == :boolean and rt == :boolean -> :boolean
      lt == :any or rt == :any -> :boolean
      true -> :error
    end
  end

  # Arithmetic operations
  def infer_expr_type({:binary_op, op, left, right}, scope)
      when op in [:add, :sub, :mul, :div] do
    lt = infer_expr_type(left, scope)
    rt = infer_expr_type(right, scope)

    cond do
      lt == :integer and rt == :integer -> :integer
      lt in [:integer, :float] and rt in [:integer, :float] -> :float
      lt == :any or rt == :any -> :any
      # String concatenation via add
      op == :add and lt == :string and rt == :string -> :string
      true -> :error
    end
  end

  # Unary operations
  def infer_expr_type({:unary_op, :not, operand}, scope) do
    case infer_expr_type(operand, scope) do
      :boolean -> :boolean
      :any -> :boolean
      _ -> :error
    end
  end

  def infer_expr_type({:unary_op, :neg, operand}, scope) do
    case infer_expr_type(operand, scope) do
      :integer -> :integer
      :float -> :float
      :any -> :any
      _ -> :error
    end
  end

  # Comparisons
  def infer_expr_type({:comparison, _op, left, right}, scope) do
    lt = infer_expr_type(left, scope)
    rt = infer_expr_type(right, scope)

    cond do
      lt == :any or rt == :any -> :boolean
      lt == rt -> :boolean
      # Allow numeric comparison across int/float
      lt in [:integer, :float] and rt in [:integer, :float] -> :boolean
      true -> :error
    end
  end

  # Module calls
  def infer_expr_type({:module_call, _path, _args}, _scope), do: :any

  # Field access
  def infer_expr_type({:field_access, _base, _field}, _scope), do: :any

  # Optional access
  def infer_expr_type({:optional_access, _base, _field}, _scope), do: :any

  # Interpolated strings
  def infer_expr_type({:interpolated_string, _parts}, _scope), do: :string

  # Fallback
  def infer_expr_type(_other, _scope), do: :any
end
