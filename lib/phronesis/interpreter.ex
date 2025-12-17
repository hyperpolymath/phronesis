# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Interpreter do
  @moduledoc """
  Interpreter for the Phronesis policy language.

  Implements the small-step operational semantics from the formal specification.

  ## Evaluation Rules

  1. **POLICY-MATCH**: If a situation matches a policy and its condition
     evaluates to true, queue the policy's action.

  2. **ACTION-EXECUTE**: An action executes only if consensus approves it,
     and it's logged immutably.

  3. **COND-TRUE/FALSE**: Standard conditional branching.

  4. **MODULE-CALL**: Module calls are evaluated externally and return
     results atomically.

  5. **CONSENSUS-VOTE**: Consensus is achieved when threshold percentage
     of agents vote true.

  ## Termination Guarantee

  Since the grammar forbids loops and recursion, all programs terminate.
  This is proven by structural induction in the formal semantics document.
  """

  alias Phronesis.{AST, State}

  @type result :: {:ok, any(), State.t()} | {:error, term()}

  @doc """
  Execute an AST program with the given state.

  Returns `{:ok, result, new_state}` on success.
  """
  @spec execute(AST.program(), State.t()) :: {:ok, State.t()} | {:error, term()}
  def execute(ast, %State{} = state) when is_list(ast) do
    Enum.reduce_while(ast, {:ok, state}, fn decl, {:ok, state} ->
      case execute_declaration(decl, state) do
        {:ok, new_state} -> {:cont, {:ok, new_state}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  @doc """
  Evaluate a policy against a situation.

  Returns `{:ok, action, new_state}` if the policy matches and should fire.
  """
  @spec evaluate_policy(AST.policy(), State.t()) ::
          {:ok, :match, AST.action(), State.t()} | {:ok, :no_match, State.t()} | {:error, term()}
  def evaluate_policy({:policy, _name, condition, action, _metadata}, state) do
    case eval_expr(condition, state) do
      {:ok, true, state} ->
        {:ok, :match, action, state}

      {:ok, false, state} ->
        {:ok, :no_match, state}

      {:ok, other, _state} ->
        {:error, {:type_error, "condition must be boolean, got: #{inspect(other)}"}}

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Execute an action with consensus checking.

  Per operational semantics Rule 2 (ACTION-EXECUTE):
  - Action must be in pending queue
  - Consensus must be approved
  - Action is logged before execution
  """
  @spec execute_action(AST.action(), State.t()) :: {:ok, any(), State.t()} | {:error, term()}
  def execute_action(action, %State{} = state) do
    # Collect votes (in real implementation, this would be distributed)
    votes = collect_votes(action, state.agents)

    if State.consensus_approved?(votes, state.agents, state.consensus_threshold) do
      # Log BEFORE execution (non-repudiation)
      state = State.log_action(state, action, votes, :approved)

      # Execute the action
      do_execute_action(action, state)
    else
      _state = State.log_action(state, action, votes, :rejected)
      {:error, {:consensus_rejected, action, votes}}
    end
  end

  # Execute declarations

  defp execute_declaration({:policy, _name, _, _, _} = policy, state) do
    {:ok, State.register_policy(state, policy)}
  end

  defp execute_declaration({:import, path, _alias}, state) do
    # Import registers module for lookup
    module_name = Enum.join(path, ".")

    case resolve_module(path) do
      {:ok, module} ->
        {:ok, State.register_module(state, path, module)}

      :error ->
        {:error, {:import_error, "module not found: #{module_name}"}}
    end
  end

  defp execute_declaration({:const, name, expr}, state) do
    case eval_expr(expr, state) do
      {:ok, value, state} ->
        {:ok, State.bind(state, name, value)}

      {:error, _} = err ->
        err
    end
  end

  # Expression evaluation

  @spec eval_expr(AST.expression(), State.t()) :: {:ok, any(), State.t()} | {:error, term()}
  defp eval_expr({:literal, _type, value}, state) do
    {:ok, value, state}
  end

  defp eval_expr({:identifier, name}, state) do
    case State.lookup(state, name) do
      {:ok, value} -> {:ok, value, state}
      :error -> {:error, {:undefined_variable, name}}
    end
  end

  defp eval_expr({:binary_op, op, left, right}, state) do
    with {:ok, l, state} <- eval_expr(left, state),
         {:ok, r, state} <- eval_expr(right, state) do
      {:ok, apply_binary_op(op, l, r), state}
    end
  end

  defp eval_expr({:unary_op, :not, operand}, state) do
    with {:ok, val, state} <- eval_expr(operand, state) do
      {:ok, not val, state}
    end
  end

  defp eval_expr({:unary_op, :neg, operand}, state) do
    with {:ok, val, state} <- eval_expr(operand, state) do
      {:ok, -val, state}
    end
  end

  defp eval_expr({:comparison, op, left, right}, state) do
    with {:ok, l, state} <- eval_expr(left, state),
         {:ok, r, state} <- eval_expr(right, state) do
      {:ok, apply_comparison(op, l, r), state}
    end
  end

  defp eval_expr({:module_call, path, args}, state) do
    with {:ok, arg_values, state} <- eval_args(args, state) do
      call_module(path, arg_values, state)
    end
  end

  # Field access: record.field (v0.2.x)
  defp eval_expr({:field_access, base, field}, state) do
    with {:ok, base_value, state} <- eval_expr(base, state) do
      case base_value do
        %{} = map ->
          field_atom = String.to_existing_atom(field)
          {:ok, Map.get(map, field_atom, Map.get(map, field)), state}

        _ ->
          {:error, {:type_error, "cannot access field '#{field}' on non-map value"}}
      end
    end
  rescue
    ArgumentError ->
      {:ok, base_value, state} = eval_expr(base, state)
      case base_value do
        %{} = map -> {:ok, Map.get(map, field), state}
        _ -> {:error, {:type_error, "cannot access field '#{field}' on non-map value"}}
      end
  end

  # Optional access: record?.field - returns nil if base is nil (v0.2.x)
  defp eval_expr({:optional_access, base, field}, state) do
    with {:ok, base_value, state} <- eval_expr(base, state) do
      case base_value do
        nil ->
          {:ok, nil, state}

        %{} = map ->
          field_atom =
            try do
              String.to_existing_atom(field)
            rescue
              ArgumentError -> nil
            end

          value = if field_atom, do: Map.get(map, field_atom, Map.get(map, field)), else: Map.get(map, field)
          {:ok, value, state}

        _ ->
          {:error, {:type_error, "cannot access field '#{field}' on non-map value"}}
      end
    end
  end

  # Interpolated string (v0.2.x)
  defp eval_expr({:interpolated_string, parts}, state) do
    eval_interpolated_parts(parts, state, [])
  end

  defp eval_interpolated_parts([], state, acc) do
    {:ok, IO.iodata_to_binary(Enum.reverse(acc)), state}
  end

  defp eval_interpolated_parts([{:string, s} | rest], state, acc) do
    eval_interpolated_parts(rest, state, [s | acc])
  end

  defp eval_interpolated_parts([{:expr, tokens} | rest], state, acc) do
    # Parse and evaluate the tokens as an expression
    case Phronesis.Parser.parse(tokens ++ [{:eof, nil, 0, 0}]) do
      {:ok, [expr]} ->
        case eval_expr(expr, state) do
          {:ok, value, state} ->
            eval_interpolated_parts(rest, state, [to_string(value) | acc])

          {:error, _} = err ->
            err
        end

      {:ok, _} ->
        {:error, {:interpolation_error, "interpolation must be a single expression"}}

      {:error, _} = err ->
        err
    end
  end

  defp eval_args(args, state) do
    Enum.reduce_while(args, {:ok, [], state}, fn
      {:named_arg, name, expr}, {:ok, acc, state} ->
        case eval_expr(expr, state) do
          {:ok, value, state} -> {:cont, {:ok, [{name, value} | acc], state}}
          {:error, _} = err -> {:halt, err}
        end

      expr, {:ok, acc, state} ->
        case eval_expr(expr, state) do
          {:ok, value, state} -> {:cont, {:ok, [value | acc], state}}
          {:error, _} = err -> {:halt, err}
        end
    end)
    |> case do
      {:ok, args, state} -> {:ok, Enum.reverse(args), state}
      error -> error
    end
  end

  # Binary operations
  defp apply_binary_op(:add, l, r), do: l + r
  defp apply_binary_op(:sub, l, r), do: l - r
  defp apply_binary_op(:mul, l, r), do: l * r
  defp apply_binary_op(:div, l, r), do: l / r
  defp apply_binary_op(:and, l, r), do: l and r
  defp apply_binary_op(:or, l, r), do: l or r

  # Comparison operations
  defp apply_comparison(:eq, l, r), do: l == r
  defp apply_comparison(:neq, l, r), do: l != r
  defp apply_comparison(:gt, l, r), do: l > r
  defp apply_comparison(:gte, l, r), do: l >= r
  defp apply_comparison(:lt, l, r), do: l < r
  defp apply_comparison(:lte, l, r), do: l <= r
  defp apply_comparison(:in, l, r) when is_list(r), do: l in r
  defp apply_comparison(:in, l, r) when is_map(r), do: Map.has_key?(r, l)

  # Action execution (after consensus)

  defp do_execute_action({:execute, function, args}, state) do
    with {:ok, arg_values, state} <- eval_args(args, state) do
      call_module([function], arg_values, state)
    end
  end

  defp do_execute_action({:report, message_expr}, state) do
    with {:ok, message, state} <- eval_expr(message_expr, state) do
      # In production, this would go to a logging system
      IO.puts("[PHRONESIS REPORT] #{message}")
      {:ok, :reported, state}
    end
  end

  defp do_execute_action({:reject, nil}, state) do
    {:ok, {:rejected, nil}, state}
  end

  defp do_execute_action({:reject, reason_expr}, state) do
    with {:ok, reason, state} <- eval_expr(reason_expr, state) do
      {:ok, {:rejected, reason}, state}
    end
  end

  defp do_execute_action({:accept, nil}, state) do
    {:ok, {:accepted, nil}, state}
  end

  defp do_execute_action({:accept, reason_expr}, state) do
    with {:ok, reason, state} <- eval_expr(reason_expr, state) do
      {:ok, {:accepted, reason}, state}
    end
  end

  defp do_execute_action({:block, actions}, state) do
    Enum.reduce_while(actions, {:ok, nil, state}, fn action, {:ok, _, state} ->
      case do_execute_action(action, state) do
        {:ok, result, state} -> {:cont, {:ok, result, state}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp do_execute_action({:conditional, condition, then_action, else_action}, state) do
    case eval_expr(condition, state) do
      {:ok, true, state} ->
        do_execute_action(then_action, state)

      {:ok, false, state} when else_action != nil ->
        do_execute_action(else_action, state)

      {:ok, false, state} ->
        {:ok, nil, state}

      {:error, _} = err ->
        err
    end
  end

  # Module system

  defp call_module(path, args, state) do
    case State.lookup_module(state, path) do
      {:ok, module} ->
        result = module.call(args)
        {:ok, result, state}

      :error ->
        # Try built-in modules
        case resolve_builtin_module(path, args) do
          {:ok, result} -> {:ok, result, state}
          :error -> {:error, {:module_not_found, Enum.join(path, ".")}}
        end
    end
  end

  defp resolve_module(["Std" | _] = path) do
    module_name = path |> Enum.join(".") |> String.replace(".", "")

    case Code.ensure_loaded(Module.concat([Phronesis, Stdlib, module_name])) do
      {:module, mod} -> {:ok, mod}
      _ -> :error
    end
  end

  defp resolve_module(_path), do: :error

  # Built-in module implementations
  defp resolve_builtin_module(["Std", "RPKI", "validate"], [_route]) do
    # Placeholder - real implementation would call RPKI validator
    {:ok, "valid"}
  end

  defp resolve_builtin_module(["Std", "BGP", "extract_as_path"], [_route]) do
    # Placeholder
    {:ok, []}
  end

  defp resolve_builtin_module(["Std", "Consensus", "require_votes"], [_action | opts]) do
    threshold = Keyword.get(opts, "threshold", 0.51)
    # Placeholder - real implementation would initiate consensus
    {:ok, threshold >= 0.5}
  end

  defp resolve_builtin_module(_, _), do: :error

  # Consensus voting (simplified for local execution)

  defp collect_votes(_action, agents) do
    # In production, this would be a distributed voting protocol (Raft/PBFT)
    # For now, local agent auto-approves
    Map.new(agents, fn agent -> {agent, true} end)
  end
end
