# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Benchmark do
  @moduledoc """
  Performance benchmarking for Phronesis.

  Measures throughput, latency, and resource usage to track
  progress toward the 10k policies/sec performance target.

  ## Usage

      # Run all benchmarks
      Phronesis.Benchmark.run_all()

      # Run specific benchmark
      Phronesis.Benchmark.run(:policy_execution)

      # Run with custom iterations
      Phronesis.Benchmark.run(:policy_execution, iterations: 100_000)

  ## Benchmarks

  - `:lexer` - Lexer tokenization throughput
  - `:parser` - Parser AST generation throughput
  - `:compiler` - Bytecode compilation throughput
  - `:interpreter` - Policy execution throughput
  - `:consensus` - Consensus voting throughput
  - `:end_to_end` - Complete pipeline throughput
  """

  require Logger
  alias Phronesis.{Lexer, Parser, Compiler, Interpreter, State}

  @default_iterations 10_000
  @target_throughput 10_000  # policies/sec

  # ============================================================
  # Public API
  # ============================================================

  @doc """
  Run all benchmarks and display results.
  """
  def run_all(opts \\ []) do
    benchmarks = [
      :lexer,
      :parser,
      :compiler,
      :interpreter,
      :consensus,
      :end_to_end
    ]

    IO.puts("\n" <> String.duplicate("=", 70))
    IO.puts("Phronesis Performance Benchmarks")
    IO.puts("Target: #{@target_throughput} policies/sec")
    IO.puts(String.duplicate("=", 70) <> "\n")

    results =
      Enum.map(benchmarks, fn benchmark ->
        result = run(benchmark, opts)
        print_result(benchmark, result)
        {benchmark, result}
      end)

    IO.puts("\n" <> String.duplicate("=", 70))
    print_summary(results)
    IO.puts(String.duplicate("=", 70) <> "\n")

    {:ok, results}
  end

  @doc """
  Run a specific benchmark.
  """
  def run(benchmark, opts \\ [])

  def run(:lexer, opts) do
    iterations = Keyword.get(opts, :iterations, @default_iterations)
    source = sample_policy()

    benchmark_fn("Lexer", iterations, fn ->
      {:ok, _tokens} = Lexer.tokenize(source)
    end)
  end

  def run(:parser, opts) do
    iterations = Keyword.get(opts, :iterations, @default_iterations)
    source = sample_policy()

    {:ok, tokens} = Lexer.tokenize(source)

    benchmark_fn("Parser", iterations, fn ->
      {:ok, _ast} = Parser.parse(tokens)
    end)
  end

  def run(:compiler, opts) do
    iterations = Keyword.get(opts, :iterations, @default_iterations)
    source = sample_policy()

    benchmark_fn("Compiler", iterations, fn ->
      {:ok, _bytecode} = Compiler.compile(source)
    end)
  end

  def run(:interpreter, opts) do
    iterations = Keyword.get(opts, :iterations, @default_iterations)
    source = sample_policy()

    {:ok, tokens} = Lexer.tokenize(source)
    {:ok, ast} = Parser.parse(tokens)
    state = State.new()

    benchmark_fn("Interpreter", iterations, fn ->
      {:ok, _state} = Interpreter.execute(ast, state)
    end)
  end

  def run(:consensus, opts) do
    iterations = Keyword.get(opts, :iterations, @default_iterations)

    benchmark_fn("Consensus", iterations, fn ->
      {:ok, _result, _votes} =
        Phronesis.Stdlib.Consensus.vote(
          {:accept, "Benchmark"},
          ["agent1", "agent2", "agent3"],
          0.67
        )
    end)
  end

  def run(:end_to_end, opts) do
    iterations = Keyword.get(opts, :iterations, @default_iterations)
    source = sample_policy()

    benchmark_fn("End-to-End", iterations, fn ->
      {:ok, tokens} = Lexer.tokenize(source)
      {:ok, ast} = Parser.parse(tokens)
      {:ok, _bytecode} = Compiler.compile(source)
      state = State.new()
      {:ok, _state} = Interpreter.execute(ast, state)
    end)
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  defp benchmark_fn(name, iterations, fun) do
    # Warmup
    Enum.each(1..100, fn _ -> fun.() end)

    # Measure
    {time_us, _} =
      :timer.tc(fn ->
        Enum.each(1..iterations, fn _ -> fun.() end)
      end)

    time_ms = time_us / 1000
    time_s = time_ms / 1000

    throughput = iterations / time_s
    latency_us = time_us / iterations

    %{
      name: name,
      iterations: iterations,
      total_time_ms: time_ms,
      throughput: throughput,
      latency_us: latency_us,
      target_throughput: @target_throughput,
      meets_target: throughput >= @target_throughput
    }
  end

  defp print_result(benchmark, result) do
    status = if result.meets_target, do: "✓", else: "✗"
    percentage = (result.throughput / result.target_throughput * 100) |> Float.round(1)

    IO.puts("#{status} #{result.name}")
    IO.puts("  Throughput: #{format_number(result.throughput)} ops/sec (#{percentage}% of target)")
    IO.puts("  Latency:    #{format_float(result.latency_us)} μs/op")
    IO.puts("  Time:       #{format_float(result.total_time_ms)} ms (#{result.iterations} iterations)")
    IO.puts("")
  end

  defp print_summary(results) do
    total_passed = Enum.count(results, fn {_, r} -> r.meets_target end)
    total_tests = length(results)

    avg_throughput =
      results
      |> Enum.map(fn {_, r} -> r.throughput end)
      |> Enum.sum()
      |> Kernel./(length(results))

    IO.puts("Summary:")
    IO.puts("  Passed: #{total_passed}/#{total_tests}")
    IO.puts("  Average throughput: #{format_number(avg_throughput)} ops/sec")

    if total_passed == total_tests do
      IO.puts("  Status: ✓ All benchmarks meet 10k ops/sec target!")
    else
      IO.puts("  Status: ✗ Some benchmarks below target")
    end
  end

  defp sample_policy do
    """
    CONST threshold = 0.75

    POLICY security_check:
      risk_level > threshold
      THEN REJECT("High risk detected")
      PRIORITY: 100
      EXPIRES: never
      CREATED_BY: benchmark
    """
  end

  defp format_number(num) when num >= 1_000_000 do
    "#{Float.round(num / 1_000_000, 2)}M"
  end

  defp format_number(num) when num >= 1_000 do
    "#{Float.round(num / 1_000, 2)}k"
  end

  defp format_number(num) do
    Float.round(num, 2)
  end

  defp format_float(num) do
    Float.round(num, 2)
  end
end
