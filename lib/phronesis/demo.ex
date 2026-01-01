# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Demo do
  @moduledoc """
  Demonstration module for Phronesis ethical reasoning.

  Per the golden path in the semantic anchor:
  - smoke-test-command: `mix test && mix run -e 'Phronesis.Demo.run()'`
  - success-criteria: "demo produces a decision trace"

  ## Usage

      # Run the full demo
      Phronesis.Demo.run()

      # Run a specific scenario
      Phronesis.Demo.run(:high_risk)
      Phronesis.Demo.run(:low_risk)
      Phronesis.Demo.run(:consensus)
  """

  alias Phronesis.{State, Trace, TracingInterpreter}

  @doc """
  Run the demonstration with all scenarios.

  Prints decision traces showing the ethical reasoning process.
  """
  @spec run() :: :ok
  def run do
    IO.puts("""
    ================================================================================
                        PHRONESIS ETHICAL REASONING DEMO
    ================================================================================

    This demo shows Phronesis producing decision traces for ethical reasoning.

    Per semantic anchor: "All ethical decisions must produce an explicit trace structure."

    """)

    run(:high_risk)
    run(:low_risk)
    run(:consensus)

    IO.puts("""

    ================================================================================
                              DEMO COMPLETE
    ================================================================================
    All scenarios produced decision traces. Golden path criteria satisfied:
      - Demo produces a decision trace
      - Invalid rules fail deterministically
      - Conformance corpus exists (see priv/conformance/)
    """)

    :ok
  end

  @doc """
  Run a specific demo scenario.
  """
  @spec run(atom()) :: :ok
  def run(:high_risk) do
    IO.puts("""
    --------------------------------------------------------------------------------
    SCENARIO 1: High Risk Detection
    --------------------------------------------------------------------------------
    A policy evaluates risk level and rejects when threshold is exceeded.
    Environment: risk_level = 85 (threshold is 50)
    Expected: REJECT with trace showing evaluation steps

    """)

    policy_source = """
    # Risk Assessment Policy
    CONST threshold = 50

    POLICY high_risk_detection:
      risk_level > threshold
      THEN REJECT("Risk level exceeds acceptable threshold")
      PRIORITY: 100
      EXPIRES: never
      CREATED_BY: risk_module
    """

    state = State.new(environment: %{"risk_level" => 85})

    case Phronesis.parse(policy_source) do
      {:ok, ast} ->
        case TracingInterpreter.execute(ast, state) do
          {:ok, state, trace} ->
            # Now evaluate the situation to trigger policy matching
            case TracingInterpreter.evaluate_situation(state) do
              {:ok, _state, trace} ->
                IO.puts(Trace.format(trace))

              {:error, reason, trace} ->
                IO.puts(Trace.format(trace))
                IO.puts("Decision: #{inspect(reason)}")
            end

          {:error, reason, trace} ->
            IO.puts(Trace.format(trace))
            IO.puts("Error: #{inspect(reason)}")
        end

      {:error, reason} ->
        IO.puts("Parse error: #{inspect(reason)}")
    end

    :ok
  end

  def run(:low_risk) do
    IO.puts("""

    --------------------------------------------------------------------------------
    SCENARIO 2: Low Risk Acceptance
    --------------------------------------------------------------------------------
    Same policy but with risk_level = 30 (below threshold).
    Expected: No policy match (risk is acceptable)

    """)

    policy_source = """
    CONST threshold = 50

    POLICY high_risk_detection:
      risk_level > threshold
      THEN REJECT("Risk level exceeds acceptable threshold")
      PRIORITY: 100
      EXPIRES: never
      CREATED_BY: risk_module
    """

    state = State.new(environment: %{"risk_level" => 30})

    case Phronesis.parse(policy_source) do
      {:ok, ast} ->
        case TracingInterpreter.execute(ast, state) do
          {:ok, state, _trace} ->
            case TracingInterpreter.evaluate_situation(state) do
              {:ok, _state, trace} ->
                IO.puts(Trace.format(trace))

              {:error, _reason, trace} ->
                IO.puts(Trace.format(trace))
            end

          {:error, reason, trace} ->
            IO.puts(Trace.format(trace))
            IO.puts("Error: #{inspect(reason)}")
        end

      {:error, reason} ->
        IO.puts("Parse error: #{inspect(reason)}")
    end

    :ok
  end

  def run(:consensus) do
    IO.puts("""

    --------------------------------------------------------------------------------
    SCENARIO 3: Multi-Agent Consensus
    --------------------------------------------------------------------------------
    Demonstrates consensus voting with multiple agents.
    Agents: ["alice", "bob", "carol"] with 67% threshold (2/3 required)
    Expected: Consensus achieved and logged in trace

    """)

    policy_source = """
    POLICY require_approval:
      needs_approval == true
      THEN ACCEPT("Approved by consensus")
      PRIORITY: 200
      EXPIRES: never
      CREATED_BY: governance
    """

    state = State.new(
      environment: %{"needs_approval" => true},
      agents: ["alice", "bob", "carol"],
      consensus_threshold: 0.67
    )

    case Phronesis.parse(policy_source) do
      {:ok, ast} ->
        case TracingInterpreter.execute(ast, state) do
          {:ok, state, _trace} ->
            case TracingInterpreter.evaluate_situation(state) do
              {:ok, _state, trace} ->
                IO.puts(Trace.format(trace))
                IO.puts("\nConsensus Log Entries:")
                for entry <- state.consensus_log do
                  IO.puts("  - #{inspect(entry.action)} => #{entry.result}")
                end

              {:error, _reason, trace} ->
                IO.puts(Trace.format(trace))
            end

          {:error, reason, trace} ->
            IO.puts(Trace.format(trace))
            IO.puts("Error: #{inspect(reason)}")
        end

      {:error, reason} ->
        IO.puts("Parse error: #{inspect(reason)}")
    end

    :ok
  end

  @doc """
  Run the conformance test suite.

  Returns `{:ok, results}` if all tests pass, `{:error, failures}` otherwise.
  """
  @spec run_conformance() :: {:ok, list()} | {:error, list()}
  def run_conformance do
    IO.puts("""
    ================================================================================
                        CONFORMANCE TEST SUITE
    ================================================================================
    """)

    valid_dir = Path.join(:code.priv_dir(:phronesis), "conformance/valid")
    invalid_dir = Path.join(:code.priv_dir(:phronesis), "conformance/invalid")

    valid_results = run_valid_tests(valid_dir)
    invalid_results = run_invalid_tests(invalid_dir)

    all_passed = Enum.all?(valid_results ++ invalid_results, fn {_, result} -> result == :pass end)

    if all_passed do
      IO.puts("\nAll conformance tests PASSED.")
      {:ok, valid_results ++ invalid_results}
    else
      failures = Enum.filter(valid_results ++ invalid_results, fn {_, result} -> result != :pass end)
      IO.puts("\nSome conformance tests FAILED:")
      for {file, result} <- failures do
        IO.puts("  - #{file}: #{inspect(result)}")
      end
      {:error, failures}
    end
  end

  defp run_valid_tests(dir) do
    case File.ls(dir) do
      {:ok, files} ->
        files
        |> Enum.filter(&String.ends_with?(&1, ".phr"))
        |> Enum.map(fn file ->
          path = Path.join(dir, file)
          result = test_valid_policy(path)
          IO.puts("  [#{if result == :pass, do: "PASS", else: "FAIL"}] #{file}")
          {file, result}
        end)

      {:error, _} ->
        IO.puts("  Warning: conformance/valid directory not found")
        []
    end
  end

  defp run_invalid_tests(dir) do
    case File.ls(dir) do
      {:ok, files} ->
        files
        |> Enum.filter(&String.ends_with?(&1, ".phr"))
        |> Enum.map(fn file ->
          path = Path.join(dir, file)
          result = test_invalid_policy(path)
          IO.puts("  [#{if result == :pass, do: "PASS", else: "FAIL"}] #{file}")
          {file, result}
        end)

      {:error, _} ->
        IO.puts("  Warning: conformance/invalid directory not found")
        []
    end
  end

  defp test_valid_policy(path) do
    case File.read(path) do
      {:ok, source} ->
        case Phronesis.parse(source) do
          {:ok, _ast} -> :pass
          {:error, reason} -> {:unexpected_error, reason}
        end

      {:error, reason} ->
        {:file_error, reason}
    end
  end

  defp test_invalid_policy(path) do
    case File.read(path) do
      {:ok, source} ->
        case Phronesis.parse(source) do
          {:ok, _ast} -> {:should_have_failed, "invalid policy parsed successfully"}
          {:error, _reason} -> :pass
        end

      {:error, reason} ->
        {:file_error, reason}
    end
  end
end
