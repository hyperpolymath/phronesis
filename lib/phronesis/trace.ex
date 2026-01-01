# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Trace do
  @moduledoc """
  Decision trace capture for ethical reasoning auditability.

  Per the semantic anchor policy: "All ethical decisions must produce
  an explicit trace structure."

  ## Trace Structure

  A trace is a chronologically-ordered list of steps, where each step
  records:
  - The operation performed (eval, match, vote, action)
  - Inputs to the operation
  - Outputs/results
  - Rationale explaining why the result occurred
  - Timestamp

  ## Example Trace

      %Phronesis.Trace{
        id: "trace-abc123",
        started_at: ~U[2026-01-01 00:00:00Z],
        completed_at: ~U[2026-01-01 00:00:01Z],
        status: :completed,
        steps: [
          %{type: :eval, expr: "x > 10", result: true, rationale: "15 > 10"},
          %{type: :match, policy: "block_high_risk", matched: true, ...},
          %{type: :vote, policy: "block_high_risk", votes: %{"local" => true}, ...},
          %{type: :action, action: :reject, reason: "High risk detected", ...}
        ],
        decision: {:reject, "High risk detected"},
        metadata: %{}
      }

  ## Usage

      trace = Phronesis.Trace.new()
      trace = Phronesis.Trace.step(trace, :eval, %{expr: "x > 10"}, true, "15 > 10")
      trace = Phronesis.Trace.complete(trace, {:accept, nil})
  """

  @type step_type :: :eval | :match | :vote | :action | :bind | :error
  @type decision :: {:accept, term()} | {:reject, term()} | {:error, term()} | nil

  @type step :: %{
          type: step_type(),
          timestamp: DateTime.t(),
          inputs: map(),
          result: term(),
          rationale: String.t()
        }

  @type t :: %__MODULE__{
          id: String.t(),
          started_at: DateTime.t(),
          completed_at: DateTime.t() | nil,
          status: :pending | :completed | :failed,
          steps: [step()],
          decision: decision(),
          metadata: map()
        }

  defstruct [
    :id,
    :started_at,
    :completed_at,
    :status,
    :steps,
    :decision,
    :metadata
  ]

  @doc """
  Create a new trace with a unique ID.
  """
  @spec new(keyword()) :: t()
  def new(opts \\ []) do
    %__MODULE__{
      id: Keyword.get(opts, :id, generate_id()),
      started_at: DateTime.utc_now(),
      completed_at: nil,
      status: :pending,
      steps: [],
      decision: nil,
      metadata: Keyword.get(opts, :metadata, %{})
    }
  end

  @doc """
  Record a step in the trace.

  ## Parameters

  - `trace` - The current trace
  - `type` - Step type (:eval, :match, :vote, :action, :bind, :error)
  - `inputs` - Map of inputs to this step
  - `result` - The result of the operation
  - `rationale` - Human-readable explanation of why this result occurred
  """
  @spec step(t(), step_type(), map(), term(), String.t()) :: t()
  def step(%__MODULE__{steps: steps} = trace, type, inputs, result, rationale) do
    new_step = %{
      type: type,
      timestamp: DateTime.utc_now(),
      inputs: inputs,
      result: result,
      rationale: rationale
    }

    %{trace | steps: steps ++ [new_step]}
  end

  @doc """
  Record an expression evaluation step.
  """
  @spec eval(t(), term(), term(), String.t()) :: t()
  def eval(trace, expr, result, rationale) do
    step(trace, :eval, %{expression: format_expr(expr)}, result, rationale)
  end

  @doc """
  Record a policy match step.
  """
  @spec match(t(), String.t(), boolean(), String.t()) :: t()
  def match(trace, policy_name, matched, rationale) do
    step(trace, :match, %{policy: policy_name}, matched, rationale)
  end

  @doc """
  Record a consensus vote step.
  """
  @spec vote(t(), term(), map(), boolean(), String.t()) :: t()
  def vote(trace, action, votes, approved, rationale) do
    step(trace, :vote, %{action: format_action(action), votes: votes}, approved, rationale)
  end

  @doc """
  Record an action execution step.
  """
  @spec action(t(), term(), term(), String.t()) :: t()
  def action(trace, action_type, result, rationale) do
    step(trace, :action, %{action: format_action(action_type)}, result, rationale)
  end

  @doc """
  Record a variable binding step.
  """
  @spec bind(t(), String.t(), term()) :: t()
  def bind(trace, name, value) do
    step(trace, :bind, %{name: name}, value, "Bound #{name} = #{inspect(value)}")
  end

  @doc """
  Record an error step.
  """
  @spec error(t(), term(), String.t()) :: t()
  def error(trace, error_term, rationale) do
    step(trace, :error, %{}, error_term, rationale)
  end

  @doc """
  Mark the trace as complete with a final decision.
  """
  @spec complete(t(), decision()) :: t()
  def complete(%__MODULE__{} = trace, decision) do
    %{trace | status: :completed, completed_at: DateTime.utc_now(), decision: decision}
  end

  @doc """
  Mark the trace as failed with an error.
  """
  @spec fail(t(), term()) :: t()
  def fail(%__MODULE__{} = trace, reason) do
    %{trace | status: :failed, completed_at: DateTime.utc_now(), decision: {:error, reason}}
  end

  @doc """
  Format the trace as a human-readable string.
  """
  @spec format(t()) :: String.t()
  def format(%__MODULE__{} = trace) do
    header = """
    ╔══════════════════════════════════════════════════════════════════╗
    ║ PHRONESIS DECISION TRACE                                        ║
    ╠══════════════════════════════════════════════════════════════════╣
    ║ ID: #{String.pad_trailing(trace.id, 54)} ║
    ║ Status: #{String.pad_trailing(to_string(trace.status), 51)} ║
    ║ Started: #{String.pad_trailing(DateTime.to_iso8601(trace.started_at), 50)} ║
    """

    completed =
      if trace.completed_at do
        "║ Completed: #{String.pad_trailing(DateTime.to_iso8601(trace.completed_at), 48)} ║\n"
      else
        ""
      end

    decision =
      case trace.decision do
        nil -> ""
        {:accept, reason} -> "║ Decision: ACCEPT #{String.pad_trailing(inspect(reason), 42)} ║\n"
        {:reject, reason} -> "║ Decision: REJECT #{String.pad_trailing(inspect(reason), 42)} ║\n"
        {:error, reason} -> "║ Decision: ERROR #{String.pad_trailing(inspect(reason), 43)} ║\n"
      end

    steps_header = """
    ╠══════════════════════════════════════════════════════════════════╣
    ║ STEPS                                                            ║
    ╠══════════════════════════════════════════════════════════════════╣
    """

    steps =
      trace.steps
      |> Enum.with_index(1)
      |> Enum.map(fn {step, idx} -> format_step(step, idx) end)
      |> Enum.join("")

    footer = """
    ╚══════════════════════════════════════════════════════════════════╝
    """

    header <> completed <> decision <> steps_header <> steps <> footer
  end

  @doc """
  Convert the trace to a JSON-serializable map.
  """
  @spec to_map(t()) :: map()
  def to_map(%__MODULE__{} = trace) do
    %{
      id: trace.id,
      started_at: DateTime.to_iso8601(trace.started_at),
      completed_at: trace.completed_at && DateTime.to_iso8601(trace.completed_at),
      status: trace.status,
      steps:
        Enum.map(trace.steps, fn step ->
          %{
            type: step.type,
            timestamp: DateTime.to_iso8601(step.timestamp),
            inputs: step.inputs,
            result: step.result,
            rationale: step.rationale
          }
        end),
      decision: format_decision(trace.decision),
      metadata: trace.metadata
    }
  end

  # Private functions

  defp generate_id do
    :crypto.strong_rand_bytes(8) |> Base.encode16(case: :lower)
  end

  defp format_step(step, idx) do
    type_str = step.type |> to_string() |> String.upcase() |> String.pad_trailing(6)
    result_str = inspect(step.result) |> String.slice(0, 40)
    rationale_str = step.rationale |> String.slice(0, 50)

    """
    ║ #{idx}. [#{type_str}] #{String.pad_trailing(result_str, 42)} ║
    ║    └─ #{String.pad_trailing(rationale_str, 55)} ║
    """
  end

  defp format_expr({:literal, _type, value}), do: inspect(value)
  defp format_expr({:identifier, name}), do: name
  defp format_expr({:binary_op, op, left, right}), do: "#{format_expr(left)} #{op} #{format_expr(right)}"
  defp format_expr({:comparison, op, left, right}), do: "#{format_expr(left)} #{op} #{format_expr(right)}"
  defp format_expr({:unary_op, op, operand}), do: "#{op} #{format_expr(operand)}"
  defp format_expr({:module_call, path, _args}), do: "#{Enum.join(path, ".")}(...)"
  defp format_expr(other), do: inspect(other)

  defp format_action({:accept, reason}), do: "ACCEPT(#{inspect(reason)})"
  defp format_action({:reject, reason}), do: "REJECT(#{inspect(reason)})"
  defp format_action({:execute, func, _args}), do: "EXECUTE(#{func})"
  defp format_action({:report, _msg}), do: "REPORT(...)"
  defp format_action({:block, _}), do: "BLOCK{...}"
  defp format_action({:conditional, _, _, _}), do: "IF...THEN...ELSE"
  defp format_action(other), do: inspect(other)

  defp format_decision(nil), do: nil
  defp format_decision({:accept, reason}), do: %{type: "accept", reason: reason}
  defp format_decision({:reject, reason}), do: %{type: "reject", reason: reason}
  defp format_decision({:error, reason}), do: %{type: "error", reason: inspect(reason)}
end
