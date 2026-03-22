#!/usr/bin/env elixir

# SPDX-License-Identifier: PMPL-1.0-or-later
# End-to-end test of phronesis policy execution

Mix.install([])

Code.prepend_path("_build/dev/lib/phronesis/ebin")

alias Phronesis.{Lexer, Parser, Interpreter, TracingInterpreter, State, Trace}

IO.puts """
================================================================================
                    PHRONESIS END-TO-END TEST
================================================================================
Testing complete policy execution pipeline: parse → execute → trace
"""

# Simple policy test
policy_source = """
# Simple AS path policy
CONST my_asn = 64512

POLICY test_policy:
  my_asn == 64512
  THEN ACCEPT("AS number matches")
  PRIORITY: 100
  EXPIRES: never
  CREATED_BY: test_suite
"""

IO.puts "\n--- Test 1: Simple Policy Execution ---"
IO.puts "Policy source:"
IO.puts policy_source

case Lexer.tokenize(policy_source) do
  {:ok, tokens} ->
    IO.puts "\n✓ Lexer succeeded (#{length(tokens)} tokens)"

    case Parser.parse(tokens) do
      {:ok, ast} ->
        IO.puts "✓ Parser succeeded"
        IO.puts "AST: #{inspect(ast, pretty: true)}"

        state = State.new(
          environment: %{},
          agents: ["alice", "bob"],
          consensus_threshold: 0.5
        )

        case TracingInterpreter.execute(ast, state) do
          {:ok, final_state, trace} ->
            IO.puts "\n✓ Execution succeeded"
            IO.puts "Final environment: #{inspect(final_state.environment)}"
            IO.puts "\nDecision trace:"
            IO.puts Trace.format(trace)

          {:error, reason, trace} ->
            IO.puts "\n✗ Execution failed: #{inspect(reason)}"
            IO.puts Trace.format(trace)
        end

      {:error, reason} ->
        IO.puts "\n✗ Parser failed: #{inspect(reason)}"
    end

  {:error, reason} ->
    IO.puts "\n✗ Lexer failed: #{inspect(reason)}"
end

# Test with BGP policy
bgp_policy = """
IMPORT Std.BGP
IMPORT Std.RPKI

CONST my_asn = 1

POLICY rpki_validation:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI validation failed")
  PRIORITY: 200
  EXPIRES: never
  CREATED_BY: security_team
"""

IO.puts """

--- Test 2: BGP Policy with Stdlib ---
Policy source:
#{bgp_policy}
"""

case Lexer.tokenize(bgp_policy) do
  {:ok, tokens} ->
    IO.puts "✓ Lexer succeeded"

    case Parser.parse(tokens) do
      {:ok, ast} ->
        IO.puts "✓ Parser succeeded"

        # Create state with a route that will trigger the policy
        state = State.new(
          environment: %{
            "route" => %{prefix: "192.0.2.0/24", origin: 99999}
          },
          agents: ["alice", "bob", "carol"],
          consensus_threshold: 0.67
        )

        case TracingInterpreter.execute(ast, state) do
          {:ok, final_state, trace} ->
            IO.puts "✓ Execution succeeded"
            IO.puts "\nFinal state:"
            IO.puts "  Policies registered: #{map_size(final_state.policy_table)}"
            IO.puts "  Environment: #{inspect(final_state.environment)}"

            IO.puts "\nNow evaluating situation..."
            case TracingInterpreter.evaluate_situation(final_state) do
              {:ok, _state, eval_trace} ->
                IO.puts "✓ Policy evaluation succeeded"
                IO.puts "\nEvaluation trace:"
                IO.puts Trace.format(eval_trace)

              {:error, reason, eval_trace} ->
                IO.puts "Policy triggered rejection: #{inspect(reason)}"
                IO.puts "\nRejection trace:"
                IO.puts Trace.format(eval_trace)
            end

          {:error, reason, trace} ->
            IO.puts "✗ Execution failed: #{inspect(reason)}"
            IO.puts Trace.format(trace)
        end

      {:error, reason} ->
        IO.puts "✗ Parser failed: #{inspect(reason)}"
    end

  {:error, reason} ->
    IO.puts "✗ Lexer failed: #{inspect(reason)}"
end

IO.puts """

================================================================================
                    END-TO-END TEST COMPLETE
================================================================================
"""
