# Testing

Testing framework and best practices for Phronesis policies.

---

## Overview

Phronesis provides a comprehensive testing framework for:

- Unit testing individual policies
- Integration testing policy sets
- Property-based testing (fuzzing)
- Regression testing

---

## Quick Start

### Write a Test

```elixir
# test/policy_test.exs
defmodule MyPolicyTest do
  use Phronesis.Test

  # Load policies before tests
  setup do
    {:ok, state} = Phronesis.load_file("policies/security.phr")
    %{state: state}
  end

  test "rejects bogon prefixes", %{state: state} do
    route = %{prefix: "10.0.0.0/24", origin_as: 65001}
    assert_reject(state, route, "Bogon prefix")
  end

  test "accepts valid routes", %{state: state} do
    route = %{prefix: "8.8.8.0/24", origin_as: 15169}
    assert_accept(state, route)
  end
end
```

### Run Tests

```bash
# Run all tests
mix test

# Run specific file
mix test test/policy_test.exs

# Run with coverage
mix test --cover
```

---

## Test Assertions

### Policy Assertions

```elixir
# Assert route is accepted
assert_accept(state, route)
assert_accept(state, route, expected_modifications)

# Assert route is rejected
assert_reject(state, route)
assert_reject(state, route, expected_reason)

# Assert specific policy matches
assert_policy_matches(state, "policy_name", route)

# Assert report generated
assert_report(state, route, expected_content)
```

### Expression Assertions

```elixir
# Assert expression evaluates to value
assert_eval(state, "1 + 2", 3)
assert_eval(state, "x > 5", true, context: %{x: 10})

# Assert expression type
assert_type(state, "42", :integer)
assert_type(state, "[1, 2]", :list)
```

---

## Test Fixtures

### Route Fixtures

```elixir
# test/support/fixtures.ex
defmodule Phronesis.Test.Fixtures do
  def valid_route do
    %{
      prefix: "8.8.8.0/24",
      prefix_length: 24,
      origin_as: 15169,
      as_path: [15169],
      next_hop: "192.0.2.1",
      local_pref: 100,
      communities: [],
      afi: "ipv4"
    }
  end

  def bogon_route do
    %{
      prefix: "10.0.0.0/24",
      prefix_length: 24,
      origin_as: 65001,
      as_path: [65001],
      afi: "ipv4"
    }
  end

  def rpki_invalid_route do
    %{
      prefix: "1.1.1.0/24",
      prefix_length: 24,
      origin_as: 99999,  # Wrong origin
      as_path: [99999],
      afi: "ipv4"
    }
  end
end
```

### Using Fixtures

```elixir
defmodule SecurityTest do
  use Phronesis.Test
  import Phronesis.Test.Fixtures

  test "rejects bogon" do
    assert_reject(@state, bogon_route(), "Bogon")
  end

  test "accepts valid route" do
    assert_accept(@state, valid_route())
  end
end
```

---

## Property-Based Testing

### Introduction

Property-based testing generates random inputs to find edge cases. Inspired by [QuickCheck](https://en.wikipedia.org/wiki/QuickCheck) and [Echidna](https://github.com/crytic/echidna).

### Basic Properties

```elixir
defmodule PropertyTest do
  use ExUnit.Case
  use Phronesis.Property

  property "bogon prefixes are always rejected" do
    check all prefix <- bogon_prefix_generator() do
      route = %{prefix: prefix, origin_as: random_as()}
      assert_reject(@state, route)
    end
  end

  property "valid RPKI routes are accepted" do
    check all route <- valid_rpki_route_generator() do
      refute_reject(@state, route, "RPKI")
    end
  end

  property "no policy causes infinite loop" do
    check all route <- any_route_generator() do
      # Should always terminate
      {result, _} = Phronesis.execute(@state, route, timeout: 1000)
      assert result in [:accept, :reject, :report]
    end
  end
end
```

### Generators

```elixir
defmodule Phronesis.Test.Generators do
  use ExUnitProperties

  # Generate random AS numbers
  def random_as do
    one_of([
      integer(1..64495),           # Public ASNs
      integer(64496..64511),       # Documentation
      integer(64512..65534),       # Private
      constant(65535)              # Reserved
    ])
  end

  # Generate random prefix
  def random_prefix do
    gen all octets <- list_of(integer(0..255), length: 4),
            length <- integer(8..32) do
      "#{Enum.join(octets, ".")}/#{length}"
    end
  end

  # Generate bogon prefixes
  def bogon_prefix_generator do
    one_of([
      constant("10.0.0.0/8"),
      constant("172.16.0.0/12"),
      constant("192.168.0.0/16"),
      gen all o2 <- integer(0..255),
              o3 <- integer(0..255),
              len <- integer(8..24) do
        "10.#{o2}.#{o3}.0/#{len}"
      end
    ])
  end

  # Generate valid route
  def valid_route_generator do
    gen all prefix <- random_prefix(),
            origin_as <- random_as(),
            path_len <- integer(1..10) do
      %{
        prefix: prefix,
        prefix_length: String.split(prefix, "/") |> List.last() |> String.to_integer(),
        origin_as: origin_as,
        as_path: Enum.take([origin_as | Enum.to_list(1..path_len)], path_len),
        afi: "ipv4"
      }
    end
  end
end
```

---

## Invariant Testing

Test that certain properties always hold:

```elixir
defmodule InvariantTest do
  use Phronesis.Test

  # Policy order invariant
  invariant "higher priority policies evaluated first" do
    policies = Phronesis.State.list_policies(@state)
    sorted = Enum.sort_by(policies, & &1.priority, :desc)
    assert policies == sorted
  end

  # Termination invariant
  invariant "all policies terminate" do
    check all route <- any_route_generator(),
              max_runs: 1000 do
      {_result, time_us} = :timer.tc(fn ->
        Phronesis.execute(@state, route)
      end)
      assert time_us < 100_000  # < 100ms
    end
  end

  # Determinism invariant
  invariant "same input produces same output" do
    check all route <- any_route_generator() do
      result1 = Phronesis.execute(@state, route)
      result2 = Phronesis.execute(@state, route)
      assert result1 == result2
    end
  end

  # Capability invariant
  invariant "no capability escalation" do
    check all route <- any_route_generator() do
      {_result, state_after} = Phronesis.execute(@state, route)
      assert state_after.capabilities == @state.capabilities
    end
  end
end
```

---

## Fuzzing

### Automated Fuzzing

```elixir
defmodule FuzzTest do
  use Phronesis.Fuzz

  # Fuzz the lexer
  fuzz "lexer handles random input" do
    input <- random_string(max_length: 10000)

    # Should not crash
    case Phronesis.Lexer.tokenize(input) do
      {:ok, _tokens} -> :ok
      {:error, _reason} -> :ok
    end
  end

  # Fuzz the parser
  fuzz "parser handles random tokens" do
    tokens <- random_token_stream(max_length: 1000)

    # Should not crash
    case Phronesis.Parser.parse(tokens) do
      {:ok, _ast} -> :ok
      {:error, _reason} -> :ok
    end
  end

  # Fuzz the interpreter
  fuzz "interpreter handles malformed routes" do
    route <- random_map(keys: route_keys(), values: any_value())

    # Should not crash, should reject or handle gracefully
    result = Phronesis.execute(@state, route)
    assert result != :crash
  end
end
```

### Corpus-Based Fuzzing

```elixir
# test/corpus/routes/valid_1.json
{"prefix": "8.8.8.0/24", "origin_as": 15169}

# test/corpus/routes/bogon_1.json
{"prefix": "10.0.0.0/8", "origin_as": 65001}

# Load corpus
defmodule CorpusTest do
  use Phronesis.Test

  @corpus_dir "test/corpus/routes"

  for file <- File.ls!(@corpus_dir) do
    @file file
    test "corpus: #{file}" do
      route = @corpus_dir
              |> Path.join(@file)
              |> File.read!()
              |> Jason.decode!()

      # Should not crash
      {result, _} = Phronesis.execute(@state, route)
      assert result in [:accept, :reject, :report]
    end
  end
end
```

---

## Coverage

### Enable Coverage

```elixir
# mix.exs
def project do
  [
    test_coverage: [tool: ExCoveralls],
    preferred_cli_env: [coveralls: :test]
  ]
end
```

### Run with Coverage

```bash
# Basic coverage
mix test --cover

# Detailed coverage report
mix coveralls.html
```

### Policy Coverage

```elixir
defmodule CoverageTest do
  use Phronesis.Test

  test "all policies are tested" do
    policies = Phronesis.State.list_policies(@state)
    tested = MapSet.new()

    # Run test suite and track which policies match
    for route <- test_routes() do
      {_result, matched_policy} = Phronesis.execute(@state, route)
      MapSet.put(tested, matched_policy)
    end

    untested = Enum.reject(policies, &(&1.name in tested))
    assert untested == [], "Untested policies: #{inspect(untested)}"
  end
end
```

---

## Mocking

### Mock RPKI

```elixir
defmodule RPKIMockTest do
  use Phronesis.Test

  setup do
    # Mock RPKI responses
    Phronesis.Mock.stub(Std.RPKI, :validate, fn route ->
      case route.origin_as do
        13335 -> "valid"
        99999 -> "invalid"
        _ -> "not_found"
      end
    end)

    :ok
  end

  test "uses mocked RPKI" do
    route = %{prefix: "1.1.1.0/24", origin_as: 99999}
    assert_reject(@state, route, "RPKI")
  end
end
```

### Mock Time

```elixir
defmodule TemporalMockTest do
  use Phronesis.Test

  test "maintenance window policy" do
    # Mock time to be within window
    Phronesis.Mock.set_time(~U[2025-01-15 03:00:00Z])

    route = valid_route()
    {result, matched} = Phronesis.execute(@state, route)

    assert matched.name == "maintenance_window"
  end
end
```

---

## CI Integration

### GitHub Actions

```yaml
# .github/workflows/test.yml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: erlef/setup-beam@v1
        with:
          otp-version: '25.0'
          elixir-version: '1.14'

      - run: mix deps.get
      - run: mix compile --warnings-as-errors
      - run: mix test --cover
      - run: mix phronesis.check policies/*.phr --strict
```

### GitLab CI

```yaml
# .gitlab-ci.yml
test:
  image: elixir:1.14
  script:
    - mix deps.get
    - mix test --cover
    - mix phronesis.check policies/*.phr
```

---

## Best Practices

### 1. Test Edge Cases

```elixir
describe "prefix length edge cases" do
  test "exactly at limit" do
    route = %{prefix: "8.8.8.0/24", prefix_length: 24}
    assert_accept(@state, route)
  end

  test "one over limit" do
    route = %{prefix: "8.8.8.0/25", prefix_length: 25}
    assert_reject(@state, route)
  end

  test "minimum prefix" do
    route = %{prefix: "8.0.0.0/8", prefix_length: 8}
    assert_accept(@state, route)
  end
end
```

### 2. Test Policy Priorities

```elixir
test "RPKI checked before bogon filter" do
  # This bogon is also RPKI invalid
  route = %{prefix: "10.0.0.0/24", origin_as: 99999}

  {_result, matched} = Phronesis.execute(@state, route)

  # Should hit RPKI first due to higher priority
  assert matched.name == "rpki_invalid"
end
```

### 3. Test State Changes

```elixir
test "consensus log is appended" do
  route = valid_route()
  initial_log_len = length(@state.consensus_log)

  {_result, new_state} = Phronesis.execute(@state, route)

  assert length(new_state.consensus_log) == initial_log_len + 1
end
```

---

## See Also

- [CLI-Reference](CLI-Reference.md) - `phronesis test` command
- [Architecture-Interpreter](Architecture-Interpreter.md) - Execution model
- [Property-Based Testing](https://hexdocs.pm/stream_data) - StreamData docs
