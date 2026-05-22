#!/usr/bin/env elixir

# SPDX-License-Identifier: MPL-2.0
# Demo of phronesis testing framework

Mix.install([])
Code.prepend_path("_build/dev/lib/phronesis/ebin")

alias Phronesis.TestFramework

IO.puts """
================================================================================
                    PHRONESIS TESTING FRAMEWORK DEMO
================================================================================
"""

# Create a simple test suite programmatically
suite = TestFramework.test_suite(
  "Simple Math Tests",
  [
    TestFramework.scenario(
      "Constant comparison",
      %{"x" => 42, "y" => 10},
      {:accept, nil}
    ),
    TestFramework.scenario(
      "Rejection test",
      %{"risk_level" => 85, "threshold" => 50},
      {:reject, "Risk too high"}
    )
  ]
)

IO.puts "\nRunning test suite programmatically..."
IO.puts "Suite: #{suite.name}"
IO.puts "Scenarios: #{length(suite.scenarios)}"

results = TestFramework.run_test_suite(suite, nil, true)

IO.puts "\n\nResults:"
Enum.each(results, fn
  {:pass, test, scenario} ->
    IO.puts "  ✓ #{test} / #{scenario}"

  {:fail, test, scenario, reason} ->
    IO.puts "  ✗ #{test} / #{scenario}: #{inspect(reason)}"

  {:error, test, scenario, error} ->
    IO.puts "  ✗ #{test} / #{scenario}: ERROR #{inspect(error)}"
end)

IO.puts """

================================================================================
                    TESTING FRAMEWORK READY
================================================================================
The testing framework is operational. Next steps:

1. Extend parser to support TEST/SCENARIO/GIVEN/EXPECT syntax
2. Add more assertion types (EXPECT_CONSENSUS, EXPECT_TRACE_CONTAINS, etc.)
3. Integrate with phronesis CLI: `phronesis test file.phr`
4. Add coverage reporting
5. Property-based testing support
"""
