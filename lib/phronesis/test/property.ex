defmodule Phronesis.Test.Property do
  @moduledoc """
  Property-based testing framework for Phronesis policies.

  Inspired by Echidna (smart contract fuzzer), this module provides:
  - Invariant testing (properties that must always hold)
  - Fuzzing with intelligent input generation
  - Shrinking to find minimal failing cases
  - Coverage-guided exploration

  ## Usage

      defmodule MyPolicyPropertyTest do
        use Phronesis.Test.Property

        # Define invariants that must always hold
        invariant "policies always terminate" do
          forall route <- route_generator() do
            {result, _time} = :timer.tc(fn ->
              Phronesis.execute(state(), route)
            end)
            result != :timeout
          end
        end

        # Property-based tests
        property "bogon prefixes are always rejected" do
          forall prefix <- bogon_prefix_generator() do
            route = %{prefix: prefix, origin_as: random_as()}
            {result, _} = Phronesis.execute(state(), route)
            result == :reject
          end
        end

        # Fuzz testing
        fuzz "interpreter handles malformed input" do
          forall input <- random_binary() do
            # Should not crash
            try do
              Phronesis.execute(state(), input)
              true
            rescue
              _ -> true  # Errors are OK, crashes are not
            end
          end
        end
      end

  ## Generators

  Built-in generators for network policy testing:

  - `route_generator/0` - Valid BGP routes
  - `bogon_prefix_generator/0` - RFC 1918 and other bogons
  - `as_number_generator/0` - Valid AS numbers
  - `ip_prefix_generator/0` - IPv4/IPv6 prefixes
  - `community_generator/0` - BGP communities

  ## Configuration

      config :phronesis, Phronesis.Test.Property,
        max_runs: 1000,
        max_shrinks: 100,
        timeout: 5000,
        seed: :random

  """

  defmacro __using__(_opts) do
    quote do
      import Phronesis.Test.Property
      import Phronesis.Test.Property.Generators
      import Phronesis.Test.Property.Assertions

      @invariants []
      @properties []
      @fuzz_tests []

      @before_compile Phronesis.Test.Property
    end
  end

  defmacro __before_compile__(_env) do
    quote do
      def __invariants__, do: @invariants
      def __properties__, do: @properties
      def __fuzz_tests__, do: @fuzz_tests
    end
  end

  @doc """
  Define an invariant that must always hold.

  Invariants are checked across all test runs and during fuzzing.
  A failing invariant indicates a fundamental violation of expected behavior.

  ## Example

      invariant "no capability escalation" do
        forall route <- route_generator() do
          {_, new_state} = Phronesis.execute(initial_state(), route)
          new_state.capabilities == initial_state().capabilities
        end
      end
  """
  defmacro invariant(name, do: block) do
    quote do
      @invariants [{unquote(name), fn -> unquote(block) end} | @invariants]

      test "invariant: #{unquote(name)}" do
        assert run_invariant(unquote(name), fn -> unquote(block) end)
      end
    end
  end

  @doc """
  Define a property-based test.

  Properties use generators to create random inputs and verify
  that a condition holds for all generated values.

  ## Example

      property "RPKI invalid routes are rejected" do
        forall route <- rpki_invalid_route_generator() do
          {result, _} = Phronesis.execute(state(), route)
          result == :reject
        end
      end
  """
  defmacro property(name, do: block) do
    quote do
      @properties [{unquote(name), fn -> unquote(block) end} | @properties]

      test "property: #{unquote(name)}" do
        assert run_property(unquote(name), fn -> unquote(block) end)
      end
    end
  end

  @doc """
  Define a fuzz test.

  Fuzz tests generate random, potentially malformed inputs
  to find crashes and unexpected behavior.

  ## Example

      fuzz "lexer handles random input" do
        forall input <- random_binary(max_size: 10000) do
          case Phronesis.Lexer.tokenize(input) do
            {:ok, _} -> true
            {:error, _} -> true
            # Crashes will fail the test
          end
        end
      end
  """
  defmacro fuzz(name, do: block) do
    quote do
      @fuzz_tests [{unquote(name), fn -> unquote(block) end} | @fuzz_tests]

      @tag :fuzz
      test "fuzz: #{unquote(name)}" do
        assert run_fuzz(unquote(name), fn -> unquote(block) end)
      end
    end
  end

  @doc """
  Universal quantification over generated values.
  """
  defmacro forall({:<-, _, [var, generator]}, do: body) do
    quote do
      run_forall(unquote(generator), fn unquote(var) -> unquote(body) end)
    end
  end

  @doc """
  Run a property test with the given generator and predicate.
  """
  def run_forall(generator, predicate, opts \\ []) do
    max_runs = Keyword.get(opts, :max_runs, config(:max_runs, 100))
    max_shrinks = Keyword.get(opts, :max_shrinks, config(:max_shrinks, 50))

    result =
      Enum.reduce_while(1..max_runs, :pass, fn run, _acc ->
        value = generate(generator)

        try do
          if predicate.(value) do
            {:cont, :pass}
          else
            # Try to shrink to minimal failing case
            minimal = shrink(generator, value, predicate, max_shrinks)
            {:halt, {:fail, minimal, run}}
          end
        rescue
          e ->
            {:halt, {:error, value, e, run}}
        end
      end)

    case result do
      :pass -> true
      {:fail, value, run} ->
        raise Phronesis.Test.Property.FailedProperty,
          message: "Property failed after #{run} runs",
          counterexample: value
      {:error, value, error, run} ->
        raise Phronesis.Test.Property.PropertyError,
          message: "Property raised error after #{run} runs",
          value: value,
          error: error
    end
  end

  @doc """
  Run an invariant check.
  """
  def run_invariant(name, check_fn) do
    case check_fn.() do
      true -> true
      false ->
        raise Phronesis.Test.Property.InvariantViolation,
          message: "Invariant '#{name}' violated"
      {:error, reason} ->
        raise Phronesis.Test.Property.InvariantViolation,
          message: "Invariant '#{name}' failed: #{inspect(reason)}"
    end
  end

  @doc """
  Run a fuzz test.
  """
  def run_fuzz(name, fuzz_fn) do
    timeout = config(:fuzz_timeout, 30_000)

    task = Task.async(fn -> fuzz_fn.() end)

    case Task.yield(task, timeout) || Task.shutdown(task) do
      {:ok, true} -> true
      {:ok, false} ->
        raise Phronesis.Test.Property.FuzzFailure,
          message: "Fuzz test '#{name}' failed"
      nil ->
        raise Phronesis.Test.Property.FuzzTimeout,
          message: "Fuzz test '#{name}' timed out after #{timeout}ms"
    end
  end

  @doc """
  Run a property test.
  """
  def run_property(name, prop_fn) do
    case prop_fn.() do
      true -> true
      false ->
        raise Phronesis.Test.Property.FailedProperty,
          message: "Property '#{name}' failed"
    end
  end

  # Generate a value from a generator
  defp generate(generator) when is_function(generator, 0), do: generator.()
  defp generate({:one_of, generators}), do: generate(Enum.random(generators))
  defp generate({:list_of, gen, opts}) do
    len = Keyword.get(opts, :length, :rand.uniform(10))
    Enum.map(1..len, fn _ -> generate(gen) end)
  end
  defp generate({:map, gen, mapper}), do: mapper.(generate(gen))
  defp generate({:filter, gen, pred}) do
    value = generate(gen)
    if pred.(value), do: value, else: generate({:filter, gen, pred})
  end
  defp generate({:integer, range}), do: Enum.random(range)
  defp generate({:constant, value}), do: value
  defp generate(value), do: value

  # Shrink a failing value to find minimal counterexample
  defp shrink(generator, value, predicate, max_attempts) do
    shrink_loop(generator, value, predicate, max_attempts, 0)
  end

  defp shrink_loop(_gen, value, _pred, max, attempts) when attempts >= max, do: value
  defp shrink_loop(generator, value, predicate, max, attempts) do
    candidates = shrink_candidates(generator, value)

    case Enum.find(candidates, fn v -> not predicate.(v) end) do
      nil -> value  # Can't shrink further
      smaller -> shrink_loop(generator, smaller, predicate, max, attempts + 1)
    end
  end

  # Generate shrink candidates
  defp shrink_candidates(_gen, value) when is_integer(value) do
    [0, div(value, 2), value - 1]
    |> Enum.filter(&(&1 >= 0 and &1 < value))
  end
  defp shrink_candidates(_gen, value) when is_binary(value) do
    len = String.length(value)
    [
      "",
      String.slice(value, 0, div(len, 2)),
      String.slice(value, 1..-1//1)
    ]
    |> Enum.filter(&(&1 != value))
  end
  defp shrink_candidates(_gen, value) when is_list(value) do
    [
      [],
      Enum.take(value, div(length(value), 2)),
      tl(value)
    ]
    |> Enum.filter(&(&1 != value and &1 != []))
  end
  defp shrink_candidates(_gen, value) when is_map(value) do
    keys = Map.keys(value)
    [
      %{},
      Map.take(value, Enum.take(keys, div(length(keys), 2)))
    ]
    |> Enum.filter(&(&1 != value))
  end
  defp shrink_candidates(_gen, _value), do: []

  defp config(key, default) do
    Application.get_env(:phronesis, __MODULE__, [])
    |> Keyword.get(key, default)
  end
end

defmodule Phronesis.Test.Property.Generators do
  @moduledoc """
  Generators for property-based testing of network policies.
  """

  @doc "Generate random AS numbers"
  def as_number_generator do
    fn ->
      Enum.random([
        Enum.random(1..64495),        # Public 2-byte
        Enum.random(64496..64511),    # Documentation
        Enum.random(64512..65534),    # Private 2-byte
        Enum.random(131072..4199999999)  # Public 4-byte
      ])
    end
  end

  @doc "Generate random IPv4 prefixes"
  def ipv4_prefix_generator do
    fn ->
      octets = Enum.map(1..4, fn _ -> :rand.uniform(256) - 1 end)
      length = :rand.uniform(25) + 7  # /8 to /32
      "#{Enum.join(octets, ".")}/#{length}"
    end
  end

  @doc "Generate bogon prefixes"
  def bogon_prefix_generator do
    {:one_of, [
      {:constant, "0.0.0.0/8"},
      {:constant, "10.0.0.0/8"},
      {:constant, "127.0.0.0/8"},
      {:constant, "169.254.0.0/16"},
      {:constant, "172.16.0.0/12"},
      {:constant, "192.168.0.0/16"},
      {:constant, "224.0.0.0/4"},
      {:constant, "240.0.0.0/4"},
      fn ->
        o2 = :rand.uniform(256) - 1
        o3 = :rand.uniform(256) - 1
        len = :rand.uniform(17) + 7
        "10.#{o2}.#{o3}.0/#{len}"
      end
    ]}
  end

  @doc "Generate valid BGP routes"
  def route_generator do
    fn ->
      prefix = generate_prefix()
      origin_as = Enum.random(1..64495)
      path_len = :rand.uniform(5)

      %{
        prefix: prefix,
        prefix_length: parse_prefix_length(prefix),
        origin_as: origin_as,
        as_path: generate_as_path(origin_as, path_len),
        next_hop: generate_next_hop(),
        local_pref: Enum.random([100, 150, 200]),
        med: :rand.uniform(1000),
        communities: generate_communities(),
        afi: "ipv4"
      }
    end
  end

  @doc "Generate RPKI-valid routes"
  def rpki_valid_route_generator do
    # Routes that should be RPKI valid (Cloudflare, Google, etc.)
    {:one_of, [
      fn -> %{prefix: "1.1.1.0/24", prefix_length: 24, origin_as: 13335, as_path: [13335], afi: "ipv4"} end,
      fn -> %{prefix: "8.8.8.0/24", prefix_length: 24, origin_as: 15169, as_path: [15169], afi: "ipv4"} end
    ]}
  end

  @doc "Generate RPKI-invalid routes"
  def rpki_invalid_route_generator do
    # Routes with wrong origin AS
    fn ->
      %{
        prefix: "1.1.1.0/24",
        prefix_length: 24,
        origin_as: 99999,  # Wrong origin
        as_path: [99999],
        afi: "ipv4"
      }
    end
  end

  @doc "Generate BGP communities"
  def community_generator do
    fn ->
      asn = Enum.random(1..65535)
      value = Enum.random(0..65535)
      "#{asn}:#{value}"
    end
  end

  @doc "Generate random binary data"
  def random_binary(opts \\ []) do
    max_size = Keyword.get(opts, :max_size, 1000)
    fn ->
      size = :rand.uniform(max_size)
      :crypto.strong_rand_bytes(size)
    end
  end

  @doc "Generate random strings"
  def random_string(opts \\ []) do
    max_length = Keyword.get(opts, :max_length, 100)
    fn ->
      length = :rand.uniform(max_length)
      chars = Enum.map(1..length, fn _ ->
        Enum.random([
          Enum.random(?a..?z),
          Enum.random(?A..?Z),
          Enum.random(?0..?9),
          Enum.random([?\s, ?\n, ?\t, ?_, ?-, ?., ?:, ?/])
        ])
      end)
      List.to_string(chars)
    end
  end

  # Helper functions
  defp generate_prefix do
    o1 = Enum.random([1, 2, 4, 8, 12, 23, 31, 45, 64, 72, 91, 104, 128, 156, 172, 185, 192, 203, 212])
    o2 = :rand.uniform(256) - 1
    o3 = :rand.uniform(256) - 1
    len = Enum.random(16..24)
    "#{o1}.#{o2}.#{o3}.0/#{len}"
  end

  defp parse_prefix_length(prefix) do
    [_, len] = String.split(prefix, "/")
    String.to_integer(len)
  end

  defp generate_as_path(origin, len) do
    path = Enum.map(1..len, fn _ -> Enum.random(1..64495) end)
    path ++ [origin]
  end

  defp generate_next_hop do
    o1 = Enum.random([192, 10, 172])
    o2 = :rand.uniform(256) - 1
    o3 = :rand.uniform(256) - 1
    o4 = Enum.random(1..254)
    "#{o1}.#{o2}.#{o3}.#{o4}"
  end

  defp generate_communities do
    count = :rand.uniform(5) - 1
    Enum.map(1..count, fn _ ->
      asn = Enum.random(1..65535)
      val = Enum.random(0..65535)
      "#{asn}:#{val}"
    end)
  end
end

defmodule Phronesis.Test.Property.Assertions do
  @moduledoc """
  Assertion helpers for property-based tests.
  """

  @doc "Assert that executing a policy accepts the route"
  defmacro assert_accepts(state, route) do
    quote do
      {result, _} = Phronesis.execute(unquote(state), unquote(route))
      assert result == :accept, "Expected ACCEPT, got #{result}"
    end
  end

  @doc "Assert that executing a policy rejects the route"
  defmacro assert_rejects(state, route) do
    quote do
      {result, _} = Phronesis.execute(unquote(state), unquote(route))
      assert result == :reject, "Expected REJECT, got #{result}"
    end
  end

  @doc "Assert execution completes within timeout"
  defmacro assert_terminates(state, route, timeout \\ 1000) do
    quote do
      task = Task.async(fn -> Phronesis.execute(unquote(state), unquote(route)) end)
      result = Task.yield(task, unquote(timeout)) || Task.shutdown(task)
      assert result != nil, "Execution did not terminate within #{unquote(timeout)}ms"
    end
  end

  @doc "Assert no capability escalation occurred"
  defmacro assert_no_escalation(state_before, state_after) do
    quote do
      assert unquote(state_after).capabilities == unquote(state_before).capabilities,
        "Capability escalation detected"
    end
  end
end

# Exception types
defmodule Phronesis.Test.Property.FailedProperty do
  defexception [:message, :counterexample]
end

defmodule Phronesis.Test.Property.PropertyError do
  defexception [:message, :value, :error]
end

defmodule Phronesis.Test.Property.InvariantViolation do
  defexception [:message]
end

defmodule Phronesis.Test.Property.FuzzFailure do
  defexception [:message]
end

defmodule Phronesis.Test.Property.FuzzTimeout do
  defexception [:message]
end
