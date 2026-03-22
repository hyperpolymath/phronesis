# SPDX-License-Identifier: PMPL-1.0-or-later
# bench_parser.exs -- Parser benchmark harness for Phronesis
#
# Generates a large synthetic Phronesis policy program and measures
# parse throughput: LOC/sec, total parse time, AST node count.
#
# Phronesis syntax: POLICY, CONST, IMPORT declarations with
# conditions (AND/OR/NOT), actions (EXECUTE, REPORT, REJECT, ACCEPT),
# and metadata (PRIORITY:).
#
# Usage:  mix run bench/bench_parser.exs

defmodule BenchParser do
  @moduledoc false

  @doc "Generate a synthetic Phronesis program with `num_policies` policy declarations."
  def generate_program(num_policies) do
    consts =
      for i <- 0..(min(num_policies, 10) - 1) do
        "CONST threshold_#{i} = #{i * 10 + 50}\n"
      end
      |> Enum.join()

    imports =
      for i <- 0..(min(num_policies, 5) - 1) do
        "IMPORT Std.Module#{i}\n"
      end
      |> Enum.join()

    policies =
      for i <- 0..(num_policies - 1) do
        action =
          case rem(i, 4) do
            0 -> "EXECUTE(handler_#{i})"
            1 -> "REPORT(\"alert #{i}\")"
            2 -> "REJECT(\"denied #{i}\")"
            3 -> "ACCEPT()"
          end

        condition =
          cond do
            rem(i, 3) == 0 ->
              "source == #{i} AND destination > #{i + 10}"
            rem(i, 3) == 1 ->
              "NOT source == #{i} OR count < #{i * 5}"
            true ->
              "value >= #{i} AND value <= #{i + 100}"
          end

        """
        POLICY check_#{i}: #{condition} THEN #{action} PRIORITY: #{rem(i, 10) + 1}
        """
      end
      |> Enum.join()

    consts <> "\n" <> imports <> "\n" <> policies
  end

  @doc "Count lines in a string."
  def count_lines(source) do
    source
    |> String.split("\n")
    |> length()
  end

  @doc "Run the benchmark."
  def run do
    num_policies = 60
    iterations = 50
    source = generate_program(num_policies)
    loc = count_lines(source)

    IO.puts("=== Phronesis Parser Benchmark ===")
    IO.puts("Source: #{loc} LOC, #{byte_size(source)} bytes")
    IO.puts("Iterations: #{iterations}\n")

    # Warm up: lex then parse
    {:ok, tokens} = Phronesis.Lexer.tokenize(source)

    case Phronesis.Parser.parse(tokens) do
      {:ok, ast} ->
        IO.puts("AST nodes (decls): #{length(ast)}")

      {:error, reason} ->
        IO.puts("Warm-up parse error: #{inspect(reason)}")
    end

    # Timed run
    {elapsed_us, _} =
      :timer.tc(fn ->
        for _ <- 1..iterations do
          {:ok, toks} = Phronesis.Lexer.tokenize(source)
          result = Phronesis.Parser.parse(toks)
          result
        end
      end)

    total_sec = elapsed_us / 1_000_000
    per_iter = total_sec / iterations
    loc_per_sec = loc * iterations / total_sec

    IO.puts("Total parse time : #{Float.round(total_sec, 4)} s")
    IO.puts("Time per parse   : #{Float.round(per_iter, 6)} s")
    IO.puts("LOC/sec          : #{Float.round(loc_per_sec, 0)}")
    IO.puts("Bytes/sec        : #{Float.round(byte_size(source) * iterations / total_sec, 0)}")
  end
end

BenchParser.run()
