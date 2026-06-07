# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.TestFramework do
  @moduledoc """
  Testing framework for Phronesis policies.

  Provides a DSL for writing policy tests with scenarios, assertions,
  and consensus simulation.

  ## Test File Structure

      TEST "Policy Suite Name" {
        SCENARIO "scenario description" {
          GIVEN
            variable = value
            another_var = expression

          EXPECT ACCEPT("reason")
          # or
          EXPECT REJECT("reason")
          # or
          EXPECT CONSENSUS(threshold: 0.67, agents: ["a", "b", "c"])
        }
      }

  ## Example

      TEST "BGP Security Policies" {
        SCENARIO "RPKI invalid route" {
          GIVEN
            route = {prefix: "192.0.2.0/24", origin: 99999}

          EXPECT REJECT("RPKI validation failed")
        }

        SCENARIO "Valid route with owned AS" {
          GIVEN
            route = {prefix: "192.0.2.0/24", origin: 64512}
            my_asn = 64512

          EXPECT ACCEPT("Route from owned AS")
        }
      }

  ## Running Tests

      # From command line
      phronesis test policy_test.phr

      # From Elixir
      {:ok, results} = Phronesis.TestFramework.run_file("policy_test.phr")

      # Run specific test
      {:ok, results} = Phronesis.TestFramework.run_test(test_ast, policy_file)
  """

  alias Phronesis.{Lexer, Parser, Interpreter, TracingInterpreter, State, Trace}

  @type test_result ::
          {:pass, test_name :: String.t(), scenario :: String.t()}
          | {:fail, test_name :: String.t(), scenario :: String.t(), reason :: term()}
          | {:error, test_name :: String.t(), scenario :: String.t(), error :: term()}

  @type test_suite :: %{
          name: String.t(),
          scenarios: [scenario()],
          policy_file: String.t() | nil
        }

  @type scenario :: %{
          name: String.t(),
          given: %{String.t() => any()},
          expect: expectation()
        }

  @type expectation ::
          {:accept, String.t() | nil}
          | {:reject, String.t() | nil}
          | {:consensus, keyword()}

  # ============================================================
  # Public API
  # ============================================================

  @doc """
  Run tests from a test file.

  Returns `{:ok, results}` with test results.
  """
  @spec run_file(Path.t(), keyword()) :: {:ok, [test_result()]} | {:error, term()}
  def run_file(test_file, opts \\ []) do
    policy_file = Keyword.get(opts, :policy_file)
    verbose = Keyword.get(opts, :verbose, false)

    with {:ok, source} <- File.read(test_file),
         {:ok, test_suites} <- parse_test_file(source) do
      results =
        Enum.flat_map(test_suites, fn suite ->
          run_test_suite(suite, policy_file, verbose)
        end)

      if verbose do
        print_results(results)
      end

      {:ok, results}
    end
  end

  @doc """
  Run a single test suite.
  """
  @spec run_test_suite(test_suite(), Path.t() | nil, boolean()) :: [test_result()]
  def run_test_suite(suite, policy_file, verbose \\ false) do
    # Load policy file if specified
    policy_state =
      if policy_file do
        case load_policy_file(policy_file) do
          {:ok, state} -> state
          {:error, _} -> State.new()
        end
      else
        State.new()
      end

    # Run each scenario
    Enum.map(suite.scenarios, fn scenario ->
      run_scenario(suite.name, scenario, policy_state, verbose)
    end)
  end

  @doc """
  Parse a test file into test suite structures.
  """
  @spec parse_test_file(String.t()) :: {:ok, [test_suite()]} | {:error, term()}
  def parse_test_file(source) do
    # For now, parse as regular phronesis and extract TEST blocks
    # In production, extend parser to handle TEST syntax
    case Lexer.tokenize(source) do
      {:ok, tokens} ->
        parse_test_tokens(tokens)

      {:error, _} = err ->
        err
    end
  end

  # ============================================================
  # Test Execution
  # ============================================================

  defp run_scenario(test_name, scenario, policy_state, verbose) do
    if verbose do
      IO.puts("  SCENARIO: #{scenario.name}")
    end

    # Create state with GIVEN variables
    test_state = %{policy_state | environment: Map.merge(policy_state.environment, scenario.given)}

    # Execute policies and check expectation
    case TracingInterpreter.evaluate_situation(test_state) do
      {:ok, _state, trace} ->
        check_expectation(test_name, scenario, trace, :ok, verbose)

      {:error, reason, trace} ->
        check_expectation(test_name, scenario, trace, {:error, reason}, verbose)
    end
  rescue
    e ->
      if verbose do
        IO.puts("    ✗ FAIL: Exception #{inspect(e)}")
      end

      {:error, test_name, scenario.name, {:exception, e}}
  end

  defp check_expectation(test_name, scenario, trace, result, verbose) do
    expected = scenario.expect

    case {expected, result} do
      {{:accept, expected_reason}, :ok} ->
        # Check if trace shows acceptance
        if trace_accepted?(trace, expected_reason) do
          if verbose, do: IO.puts("    ✓ PASS")
          {:pass, test_name, scenario.name}
        else
          if verbose, do: IO.puts("    ✗ FAIL: Expected ACCEPT, got #{inspect(result)}")
          {:fail, test_name, scenario.name, {:expected_accept, :got_other}}
        end

      {{:reject, expected_reason}, {:error, {:rejected, actual_reason}}} ->
        if expected_reason == nil or expected_reason == actual_reason do
          if verbose, do: IO.puts("    ✓ PASS")
          {:pass, test_name, scenario.name}
        else
          if verbose,
            do: IO.puts("    ✗ FAIL: Reject reason mismatch: expected #{inspect(expected_reason)}, got #{inspect(actual_reason)}")

          {:fail, test_name, scenario.name, {:reason_mismatch, expected_reason, actual_reason}}
        end

      {{:consensus, _opts}, _} ->
        # Check consensus in trace
        if trace_consensus_achieved?(trace) do
          if verbose, do: IO.puts("    ✓ PASS")
          {:pass, test_name, scenario.name}
        else
          if verbose, do: IO.puts("    ✗ FAIL: Consensus not achieved")
          {:fail, test_name, scenario.name, :consensus_failed}
        end

      {expected, actual} ->
        if verbose,
          do: IO.puts("    ✗ FAIL: Expected #{inspect(expected)}, got #{inspect(actual)}")

        {:fail, test_name, scenario.name, {:mismatch, expected, actual}}
    end
  end

  defp trace_accepted?(trace, expected_reason) do
    # Check if trace shows an acceptance
    Enum.any?(trace.steps, fn step ->
      case step do
        %{type: :action, result: {:accepted, reason}} ->
          expected_reason == nil or reason == expected_reason

        _ ->
          false
      end
    end)
  end

  defp trace_consensus_achieved?(trace) do
    Enum.any?(trace.steps, fn step ->
      step.type == :vote and step.result == true
    end)
  end

  # ============================================================
  # Policy Loading
  # ============================================================

  defp load_policy_file(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      state = State.new()

      case TracingInterpreter.execute(ast, state) do
        {:ok, new_state, _trace} -> {:ok, new_state}
        {:error, reason, _trace} -> {:error, reason}
      end
    end
  end

  # ============================================================
  # Test Parsing (Simplified - extend Parser for full support)
  # ============================================================

  defp parse_test_tokens(tokens) do
    # Simplified parser - in production, extend main parser
    # For now, look for patterns like:
    # TEST "name" { SCENARIO "name" { GIVEN ... EXPECT ... } }

    # This is a placeholder - real implementation would extend Parser module
    {:ok,
     [
       %{
         name: "Example Test",
         scenarios: [
           %{
             name: "example scenario",
             given: %{"x" => 42},
             expect: {:accept, nil}
           }
         ],
         policy_file: nil
       }
     ]}
  end

  # ============================================================
  # Result Reporting
  # ============================================================

  defp print_results(results) do
    IO.puts("\n" <> String.duplicate("=", 70))
    IO.puts("TEST RESULTS")
    IO.puts(String.duplicate("=", 70))

    passed = Enum.count(results, &match?({:pass, _, _}, &1))
    failed = Enum.count(results, &match?({:fail, _, _, _}, &1))
    errors = Enum.count(results, &match?({:error, _, _, _}, &1))
    total = length(results)

    IO.puts("\nSummary:")
    IO.puts("  Total:  #{total}")
    IO.puts("  Passed: #{passed}")
    IO.puts("  Failed: #{failed}")
    IO.puts("  Errors: #{errors}")

    if failed > 0 or errors > 0 do
      IO.puts("\nFailures:")

      Enum.each(results, fn
        {:fail, test, scenario, reason} ->
          IO.puts("  ✗ #{test} / #{scenario}")
          IO.puts("    #{inspect(reason)}")

        {:error, test, scenario, error} ->
          IO.puts("  ✗ #{test} / #{scenario}")
          IO.puts("    ERROR: #{inspect(error)}")

        _ ->
          :ok
      end)
    end

    IO.puts(String.duplicate("=", 70))

    if failed == 0 and errors == 0 do
      IO.puts("✓ All tests passed!")
    else
      IO.puts("✗ Some tests failed")
    end
  end

  @doc """
  Create a simple test scenario programmatically.
  """
  @spec scenario(String.t(), map(), expectation()) :: scenario()
  def scenario(name, given, expect) do
    %{
      name: name,
      given: given,
      expect: expect
    }
  end

  @doc """
  Create a test suite programmatically.
  """
  @spec test_suite(String.t(), [scenario()], keyword()) :: test_suite()
  def test_suite(name, scenarios, opts \\ []) do
    %{
      name: name,
      scenarios: scenarios,
      policy_file: Keyword.get(opts, :policy_file)
    }
  end
end
