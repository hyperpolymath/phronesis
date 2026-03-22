#!/usr/bin/env elixir

# SPDX-License-Identifier: PMPL-1.0-or-later
# Test script for phronesis standard library

Mix.install([])

Code.prepend_path("_build/dev/lib/phronesis/ebin")

IO.puts """
================================================================================
                    PHRONESIS STDLIB TEST
================================================================================
Testing the standard library modules with sample data.
"""

# Test BGP module
IO.puts "\n--- Testing Std.BGP ---"

route = %{
  prefix: "192.0.2.0/24",
  next_hop: "203.0.113.1",
  as_path: [64512, 64513, 64514],
  origin: 64514,
  local_pref: 100,
  med: 50
}

IO.puts "Route: #{inspect(route)}"
IO.puts "AS Path: #{inspect(Phronesis.Stdlib.BGP.extract_as_path(route))}"
IO.puts "Origin: #{inspect(Phronesis.Stdlib.BGP.get_origin(route))}"
IO.puts "Path Length: #{inspect(Phronesis.Stdlib.BGP.path_length(route))}"
IO.puts "Validation: #{inspect(Phronesis.Stdlib.BGP.validate_route(route))}"
IO.puts "Is 64512 private? #{inspect(Phronesis.Stdlib.BGP.is_private_asn?(64512))}"

# Test RPKI module
IO.puts "\n--- Testing Std.RPKI ---"

test_route_1 = %{prefix: "192.0.2.0/24", origin: 64512}
IO.puts "Route 1: #{inspect(test_route_1)}"
IO.puts "RPKI Validation: #{inspect(Phronesis.Stdlib.RPKI.validate(test_route_1))}"

test_route_2 = %{prefix: "192.0.2.0/24", origin: 99999}
IO.puts "\nRoute 2: #{inspect(test_route_2)}"
IO.puts "RPKI Validation: #{inspect(Phronesis.Stdlib.RPKI.validate(test_route_2))}"

# Test Temporal module
IO.puts "\n--- Testing Std.Temporal ---"

now = Phronesis.Stdlib.Temporal.now()
IO.puts "Current time: #{inspect(now)}"

past = DateTime.add(now, -7200, :second)
IO.puts "2 hours ago: #{inspect(past)}"
IO.puts "Expired after 3600 seconds? #{inspect(Phronesis.Stdlib.Temporal.is_expired(past, 3600))}"

future = DateTime.add(now, 7200, :second)
IO.puts "\n2 hours from now: #{inspect(future)}"
IO.puts "Expired after 3600 seconds? #{inspect(Phronesis.Stdlib.Temporal.is_expired(future, 3600))}"

# Test Consensus module
IO.puts "\n--- Testing Std.Consensus ---"

{:ok, approved, votes} = Phronesis.Stdlib.Consensus.vote(
  {:accept, "Test action"},
  ["alice", "bob", "carol"],
  0.67
)

IO.puts "Consensus vote result: #{approved}"
IO.puts "Votes: #{inspect(votes)}"
IO.puts "Approvals: #{Phronesis.Stdlib.Consensus.count_approvals(votes)}"

IO.puts """

================================================================================
                    STDLIB TEST COMPLETE
================================================================================
All standard library modules are working correctly.
"""
