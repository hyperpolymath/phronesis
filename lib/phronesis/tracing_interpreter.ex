# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.TracingInterpreter do
  @moduledoc """
  Interpreter wrapper that captures decision traces.

  This module wraps the core Phronesis.Interpreter to capture
  a full trace of all ethical decisions made during execution.

  Per the semantic anchor: "All ethical decisions must produce
  an explicit trace structure."

  ## Usage

      state = Phronesis.State.new(environment: %{"risk_level" => 75})
      {:ok, ast} = Phronesis.parse("POLICY high_risk: risk_level > 50 THEN REJECT(...)")

      case Phronesis.TracingInterpreter.execute(ast, state) do
        {:ok, state, trace} ->
          IO.puts(Phronesis.Trace.format(trace))
        {:error, reason, trace} ->
          IO.puts("Error: \#{inspect(reason)}")
          IO.puts(Phronesis.Trace.format(trace))
      end
  """

  alias Phronesis.{AST, State, Trace, Interpreter}

  @type result :: {:ok, State.t(), Trace.t()} | {:error, term(), Trace.t()}

  @doc """
  Execute an AST program with tracing enabled.

  Returns `{:ok, new_state, trace}` on success, or `{:error, reason, trace}` on failure.
  The trace is always returned, even on error, for auditability.
  """
  @spec execute(AST.program(), State.t(), keyword()) :: result()
  def execute(ast, %State{} = state, opts \\ []) when is_list(ast) do
    trace = Trace.new(Keyword.take(opts, [:id, :metadata]))

    case execute_with_trace(ast, state, trace) do
      {:ok, state, trace} ->
        decision = determine_decision(state)
        {:ok, state, Trace.complete(trace, decision)}

      {:error, reason, trace} ->
        {:error, reason, Trace.fail(trace, reason)}
    end
  end

  @doc """
  Evaluate policies against a situation and trace the decision process.

  Returns the first matching policy's action result along with the trace.
  """
  @spec evaluate_situation(State.t(), keyword()) :: result()
  def evaluate_situation(%State{} = state, opts \\ []) do
    trace = Trace.new(Keyword.take(opts, [:id, :metadata]))
    policies = State.policies_by_priority(state)

    trace = Trace.step(trace, :eval, %{operation: "evaluate_situation"}, length(policies),
      "Evaluating #{length(policies)} policies by priority order")

    evaluate_policies(policies, state, trace)
  end

  # Private implementation

  defp execute_with_trace([], state, trace) do
    {:ok, state, trace}
  end

  defp execute_with_trace([decl | rest], state, trace) do
    case execute_declaration_traced(decl, state, trace) do
      {:ok, new_state, new_trace} ->
        execute_with_trace(rest, new_state, new_trace)

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp execute_declaration_traced({:policy, name, condition, action, metadata} = policy, state, trace) do
    trace = Trace.step(trace, :eval, %{policy: name, condition: format_expr(condition)}, :registered,
      "Registering policy '#{name}' with priority #{metadata[:priority] || 0}")

    {:ok, State.register_policy(state, policy), trace}
  end

  defp execute_declaration_traced({:import, path, _alias}, state, trace) do
    module_name = Enum.join(path, ".")
    trace = Trace.step(trace, :eval, %{import: module_name}, :imported,
      "Importing module #{module_name}")

    case Interpreter.execute([{:import, path, nil}], state) do
      {:ok, new_state} -> {:ok, new_state, trace}
      {:error, reason} -> {:error, reason, Trace.error(trace, reason, "Import failed: #{module_name}")}
    end
  end

  defp execute_declaration_traced({:const, name, expr}, state, trace) do
    case eval_expr_traced(expr, state, trace) do
      {:ok, value, state, trace} ->
        trace = Trace.bind(trace, name, value)
        {:ok, State.bind(state, name, value), trace}

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp eval_expr_traced({:literal, _type, value} = expr, state, trace) do
    trace = Trace.eval(trace, expr, value, "Literal value: #{inspect(value)}")
    {:ok, value, state, trace}
  end

  defp eval_expr_traced({:identifier, name} = expr, state, trace) do
    case State.lookup(state, name) do
      {:ok, value} ->
        trace = Trace.eval(trace, expr, value, "Variable '#{name}' resolved to #{inspect(value)}")
        {:ok, value, state, trace}

      :error ->
        trace = Trace.error(trace, {:undefined_variable, name}, "Variable '#{name}' is not defined")
        {:error, {:undefined_variable, name}, trace}
    end
  end

  defp eval_expr_traced({:binary_op, op, left, right}, state, trace) do
    with {:ok, l, state, trace} <- eval_expr_traced(left, state, trace),
         {:ok, r, state, trace} <- eval_expr_traced(right, state, trace) do
      result = apply_binary_op(op, l, r)
      trace = Trace.eval(trace, {:binary_op, op, left, right}, result,
        "#{inspect(l)} #{op} #{inspect(r)} = #{inspect(result)}")
      {:ok, result, state, trace}
    end
  end

  defp eval_expr_traced({:comparison, op, left, right}, state, trace) do
    with {:ok, l, state, trace} <- eval_expr_traced(left, state, trace),
         {:ok, r, state, trace} <- eval_expr_traced(right, state, trace) do
      result = apply_comparison(op, l, r)
      rationale = "#{inspect(l)} #{format_comparison_op(op)} #{inspect(r)} = #{result}"
      trace = Trace.eval(trace, {:comparison, op, left, right}, result, rationale)
      {:ok, result, state, trace}
    end
  end

  defp eval_expr_traced({:unary_op, :not, operand}, state, trace) do
    with {:ok, val, state, trace} <- eval_expr_traced(operand, state, trace) do
      result = not val
      trace = Trace.eval(trace, {:unary_op, :not, operand}, result, "NOT #{inspect(val)} = #{result}")
      {:ok, result, state, trace}
    end
  end

  defp eval_expr_traced({:unary_op, :neg, operand}, state, trace) do
    with {:ok, val, state, trace} <- eval_expr_traced(operand, state, trace) do
      result = -val
      trace = Trace.eval(trace, {:unary_op, :neg, operand}, result, "-#{inspect(val)} = #{result}")
      {:ok, result, state, trace}
    end
  end

  defp eval_expr_traced({:module_call, path, args}, state, trace) do
    func_name = Enum.join(path, ".")
    # Evaluate args
    case eval_args_traced(args, state, trace) do
      {:ok, arg_values, state, trace} ->
        case Interpreter.call_module_public(path, arg_values, state) do
          {:ok, result, state} ->
            trace = Trace.eval(trace, {:module_call, path, args}, result,
              "Called #{func_name}(#{inspect(arg_values)}) -> #{inspect(result)}")
            {:ok, result, state, trace}

          {:error, reason} ->
            trace = Trace.error(trace, reason, "Module call failed: #{func_name}")
            {:error, reason, trace}
        end

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp eval_expr_traced(expr, state, trace) do
    # Fallback for other expression types - delegate to base interpreter
    case eval_with_interpreter(expr, state) do
      {:ok, value, state} ->
        trace = Trace.eval(trace, expr, value, "Evaluated expression: #{inspect(value)}")
        {:ok, value, state, trace}

      {:error, reason} ->
        trace = Trace.error(trace, reason, "Expression evaluation failed")
        {:error, reason, trace}
    end
  end

  defp eval_args_traced(args, state, trace) do
    Enum.reduce_while(args, {:ok, [], state, trace}, fn
      {:named_arg, name, expr}, {:ok, acc, state, trace} ->
        case eval_expr_traced(expr, state, trace) do
          {:ok, value, state, trace} -> {:cont, {:ok, [{name, value} | acc], state, trace}}
          {:error, _, _} = err -> {:halt, err}
        end

      expr, {:ok, acc, state, trace} ->
        case eval_expr_traced(expr, state, trace) do
          {:ok, value, state, trace} -> {:cont, {:ok, [value | acc], state, trace}}
          {:error, _, _} = err -> {:halt, err}
        end
    end)
    |> case do
      {:ok, args, state, trace} -> {:ok, Enum.reverse(args), state, trace}
      error -> error
    end
  end

  defp evaluate_policies([], state, trace) do
    trace = Trace.step(trace, :match, %{result: "no_match"}, nil,
      "No policies matched the current situation")
    {:ok, state, Trace.complete(trace, nil)}
  end

  defp evaluate_policies([{:policy, name, condition, action, _meta} | rest], state, trace) do
    case eval_expr_traced(condition, state, trace) do
      {:ok, true, state, trace} ->
        trace = Trace.match(trace, name, true, "Policy '#{name}' condition evaluated to true")
        execute_action_traced(action, name, state, trace)

      {:ok, false, state, trace} ->
        trace = Trace.match(trace, name, false, "Policy '#{name}' condition evaluated to false")
        evaluate_policies(rest, state, trace)

      {:ok, other, _state, trace} ->
        trace = Trace.error(trace, {:type_error, name, other},
          "Policy '#{name}' condition must be boolean, got: #{inspect(other)}")
        {:error, {:type_error, "condition must be boolean"}, trace}

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp execute_action_traced(action, policy_name, state, trace) do
    # Collect votes
    votes = collect_votes(action, state.agents)
    approved = State.consensus_approved?(votes, state.agents, state.consensus_threshold)

    vote_summary = "#{Enum.count(votes, fn {_, v} -> v end)}/#{length(state.agents)} approved"
    trace = Trace.vote(trace, action, votes, approved,
      "Consensus for '#{policy_name}': #{vote_summary} (threshold: #{state.consensus_threshold * 100}%)")

    if approved do
      state = State.log_action(state, action, votes, :approved)
      execute_action_impl(action, state, trace)
    else
      state = State.log_action(state, action, votes, :rejected)
      trace = Trace.action(trace, action, {:rejected, :consensus_failed},
        "Action rejected: consensus not achieved")
      {:error, {:consensus_rejected, action, votes}, trace}
    end
  end

  defp execute_action_impl({:accept, reason_expr}, state, trace) do
    case eval_reason(reason_expr, state, trace) do
      {:ok, reason, state, trace} ->
        trace = Trace.action(trace, {:accept, reason}, {:accepted, reason}, "Accepted: #{inspect(reason)}")
        {:ok, state, Trace.complete(trace, {:accept, reason})}

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp execute_action_impl({:reject, reason_expr}, state, trace) do
    case eval_reason(reason_expr, state, trace) do
      {:ok, reason, state, trace} ->
        trace = Trace.action(trace, {:reject, reason}, {:rejected, reason}, "Rejected: #{inspect(reason)}")
        {:ok, state, Trace.complete(trace, {:reject, reason})}

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp execute_action_impl({:report, msg_expr}, state, trace) do
    case eval_expr_traced(msg_expr, state, trace) do
      {:ok, message, state, trace} ->
        IO.puts("[PHRONESIS REPORT] #{message}")
        trace = Trace.action(trace, {:report, message}, :reported, "Reported: #{message}")
        {:ok, state, trace}

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp execute_action_impl({:execute, func, args}, state, trace) do
    case eval_args_traced(args, state, trace) do
      {:ok, arg_values, state, trace} ->
        case Interpreter.call_module_public([func], arg_values, state) do
          {:ok, result, state} ->
            trace = Trace.action(trace, {:execute, func, args}, result, "Executed #{func}: #{inspect(result)}")
            {:ok, state, trace}

          {:error, reason} ->
            trace = Trace.error(trace, reason, "Execution failed: #{func}")
            {:error, reason, trace}
        end

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp execute_action_impl({:block, actions}, state, trace) do
    trace = Trace.step(trace, :action, %{block_size: length(actions)}, :entering_block,
      "Executing block of #{length(actions)} actions")

    Enum.reduce_while(actions, {:ok, state, trace}, fn action, {:ok, state, trace} ->
      case execute_action_impl(action, state, trace) do
        {:ok, state, trace} -> {:cont, {:ok, state, trace}}
        {:error, reason, trace} -> {:halt, {:error, reason, trace}}
      end
    end)
  end

  defp execute_action_impl({:conditional, cond_expr, then_action, else_action}, state, trace) do
    case eval_expr_traced(cond_expr, state, trace) do
      {:ok, true, state, trace} ->
        trace = Trace.step(trace, :eval, %{conditional: "then_branch"}, true,
          "Conditional evaluated to true, taking THEN branch")
        execute_action_impl(then_action, state, trace)

      {:ok, false, state, trace} when else_action != nil ->
        trace = Trace.step(trace, :eval, %{conditional: "else_branch"}, false,
          "Conditional evaluated to false, taking ELSE branch")
        execute_action_impl(else_action, state, trace)

      {:ok, false, state, trace} ->
        trace = Trace.step(trace, :eval, %{conditional: "no_else"}, false,
          "Conditional evaluated to false, no ELSE branch")
        {:ok, state, trace}

      {:error, reason, trace} ->
        {:error, reason, trace}
    end
  end

  defp eval_reason(nil, state, trace), do: {:ok, nil, state, trace}
  defp eval_reason(expr, state, trace), do: eval_expr_traced(expr, state, trace)

  defp eval_with_interpreter(expr, state) do
    # Create a temporary AST to evaluate just this expression
    # We use the const mechanism since it evaluates an expression
    temp_name = "__eval_temp_#{:erlang.unique_integer([:positive])}"
    ast = [{:const, temp_name, expr}]

    case Interpreter.execute(ast, state) do
      {:ok, new_state} ->
        {:ok, value} = State.lookup(new_state, temp_name)
        {:ok, value, state}

      {:error, _} = err ->
        err
    end
  end

  defp collect_votes(_action, agents) do
    Map.new(agents, fn agent -> {agent, true} end)
  end

  defp determine_decision(%State{consensus_log: log}) do
    case log do
      [%{action: {:accept, reason}, result: :approved} | _] -> {:accept, reason}
      [%{action: {:reject, reason}, result: :approved} | _] -> {:reject, reason}
      _ -> nil
    end
  end

  defp apply_binary_op(:add, l, r), do: l + r
  defp apply_binary_op(:sub, l, r), do: l - r
  defp apply_binary_op(:mul, l, r), do: l * r
  defp apply_binary_op(:div, l, r), do: l / r
  defp apply_binary_op(:and, l, r), do: l and r
  defp apply_binary_op(:or, l, r), do: l or r

  defp apply_comparison(:eq, l, r), do: l == r
  defp apply_comparison(:neq, l, r), do: l != r
  defp apply_comparison(:gt, l, r), do: l > r
  defp apply_comparison(:gte, l, r), do: l >= r
  defp apply_comparison(:lt, l, r), do: l < r
  defp apply_comparison(:lte, l, r), do: l <= r
  defp apply_comparison(:in, l, r) when is_list(r), do: l in r
  defp apply_comparison(:in, l, r) when is_map(r), do: Map.has_key?(r, l)

  defp format_comparison_op(:eq), do: "=="
  defp format_comparison_op(:neq), do: "!="
  defp format_comparison_op(:gt), do: ">"
  defp format_comparison_op(:gte), do: ">="
  defp format_comparison_op(:lt), do: "<"
  defp format_comparison_op(:lte), do: "<="
  defp format_comparison_op(:in), do: "IN"

  defp format_expr({:literal, _type, value}), do: inspect(value)
  defp format_expr({:identifier, name}), do: name
  defp format_expr({:binary_op, op, left, right}), do: "#{format_expr(left)} #{op} #{format_expr(right)}"
  defp format_expr({:comparison, op, left, right}), do: "#{format_expr(left)} #{format_comparison_op(op)} #{format_expr(right)}"
  defp format_expr({:unary_op, op, operand}), do: "#{op}(#{format_expr(operand)})"
  defp format_expr({:module_call, path, _args}), do: "#{Enum.join(path, ".")}(...)"
  defp format_expr(other), do: inspect(other)
end
