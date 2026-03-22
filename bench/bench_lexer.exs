# SPDX-License-Identifier: PMPL-1.0-or-later
# bench_lexer.exs -- Lexer performance benchmark for Phronesis
#
# Measures:
#   - Tokens per second on synthetic source (10K+ tokens)
#   - Time to lex an empty file vs a large file
#   - Memory allocation per token (via :erlang.process_info)
#
# Run:
#   mix run bench/bench_lexer.exs

defmodule BenchLexer do
  @moduledoc """
  Benchmark harness for the Phronesis lexer.
  """

  @iterations 100

  @doc """
  Generate a realistic Phronesis policy source string.
  Uses Phronesis keywords (POLICY, THEN, AND, OR, etc.), operators,
  and various literal types.
  """
  def generate_source(num_statements) do
    keywords = [
      "POLICY", "THEN", "AND", "OR", "NOT", "ACCEPT", "REJECT", "REPORT",
      "EXECUTE", "IF", "ELSE", "CONST", "IMPORT", "AS", "PRIORITY"
    ]

    operators = [
      "==", "!=", ">=", "<=", "?.", "??", ">", "<", "+", "-", "*", "/",
      "%", "="
    ]

    0..(num_statements - 1)
    |> Enum.map(fn i ->
      kw = Enum.at(keywords, rem(i, length(keywords)))
      op = Enum.at(operators, rem(i, length(operators)))

      line = "#{kw} rule_#{i} #{op} #{i * 42};\n"

      extra =
        if rem(i, 10) == 0 do
          """
          # line comment
          "string_literal_#{i}"
          192.168.#{rem(i, 256)}.1
          { [ ( ) ] } , : .
          """
        else
          ""
        end

      line <> extra
    end)
    |> Enum.join()
  end

  @doc """
  Count tokens produced by the Phronesis lexer.
  """
  def count_tokens(source) do
    case Phronesis.Lexer.tokenize(source) do
      {:ok, tokens} -> length(tokens)
      {:error, _} -> 0
    end
  end

  @doc """
  Time a function, returning {result, elapsed_microseconds}.
  """
  def time_it(fun) do
    {elapsed_us, result} = :timer.tc(fun)
    {result, elapsed_us}
  end

  @doc """
  Measure memory allocated during a function call (heap words delta).
  """
  def measure_memory(fun) do
    :erlang.garbage_collect()
    {:memory, mem_before} = :erlang.process_info(self(), :memory)
    result = fun.()
    {:memory, mem_after} = :erlang.process_info(self(), :memory)
    {result, max(mem_after - mem_before, 0)}
  end

  def run do
    IO.puts("=== Phronesis Lexer Benchmark ===\n")

    # --- Benchmark 1: Empty file ---
    {_, empty_us} = time_it(fn ->
      for _ <- 1..@iterations, do: count_tokens("")
    end)

    IO.puts("Empty file:")
    IO.puts("  #{@iterations} iterations in #{Float.round(empty_us / 1_000_000, 4)} s " <>
            "(#{Float.round(empty_us / @iterations, 2)} us/iter)")

    # --- Generate large source ---
    source = generate_source(2000)
    source_bytes = byte_size(source)
    token_count = count_tokens(source)
    IO.puts("\nLarge file (#{source_bytes} bytes, #{token_count} tokens):")

    # --- Benchmark 2: Tokens/sec on large file ---
    {_, large_us} = time_it(fn ->
      for _ <- 1..@iterations, do: count_tokens(source)
    end)

    large_sec = large_us / 1_000_000
    total_tokens = token_count * @iterations
    tokens_per_sec = total_tokens / large_sec

    IO.puts("  #{@iterations} iterations in #{Float.round(large_sec, 4)} s")
    IO.puts("  #{Float.round(tokens_per_sec, 2)} tokens/sec")
    IO.puts("  #{Float.round(large_us / total_tokens, 2)} us/token")
    IO.puts("  #{Float.round(source_bytes * @iterations / large_sec / 1_000_000, 2)} MB/sec")

    # --- Benchmark 3: Memory allocation per token ---
    {_, mem_delta} = measure_memory(fn ->
      count_tokens(source)
    end)

    IO.puts("\nMemory allocation:")
    IO.puts("  #{token_count} tokens produced")
    IO.puts("  Heap delta: #{mem_delta} bytes " <>
            "(#{Float.round(mem_delta / max(token_count, 1), 1)} bytes/token)")

    IO.puts("\nDone.")
  end
end

BenchLexer.run()
