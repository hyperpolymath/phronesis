# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2026 Phronesis Contributors
#
# Fuzz test for the Phronesis lexer.
#
# Invariant: the lexer must NEVER crash on ANY input. It should always
# return {:ok, tokens} or {:error, {...}} without raising an exception.
#
# This test generates random strings (both pure random bytes and
# fragment-based inputs biased toward Phronesis tokens) and feeds
# them to Phronesis.Lexer.tokenize/1.
#
# Run with:
#   mix test test/fuzz/lexer_fuzz_test.exs
#
# Increase iterations via environment variable:
#   FUZZ_ITERATIONS=500000 mix test test/fuzz/lexer_fuzz_test.exs

defmodule Phronesis.Lexer.FuzzTest do
  use ExUnit.Case, async: true

  @moduledoc """
  Property-based fuzz testing for the Phronesis lexer.
  Generates random inputs and asserts the lexer never crashes.
  """

  # Interesting fragments biased toward Phronesis syntax
  @fragments [
    # Keywords
    "POLICY", "THEN", "AND", "OR", "NOT", "ACCEPT", "REJECT",
    "REPORT", "EXECUTE", "IF", "ELSE", "CONST", "IMPORT", "AS",
    "PRIORITY",
    # Operators
    "==", "!=", ">=", "<=", ">", "<", "+", "-", "*", "/", "%",
    "?.", "??", "=",
    # Delimiters
    "(", ")", "[", "]", "{", "}", ",", ":", ".", "::",
    # Literals
    "42", "0", "999", "3.14", "1.5e10", "3e-5",
    "0xFF", "0xDEADBEEF", "0b1010", "0o755",
    ~s("hello"), ~s("escape\\n"), ~s(r"raw string"),
    ~s("""\nmultiline\n"""),
    # IP addresses
    "192.168.1.1", "10.0.0.0/8", "2001:db8::1", "::1", "fe80::/10",
    # DateTime
    "2025-01-15T10:30:00Z",
    # Identifiers
    "foo", "bar_baz", "MyPolicy", "_private",
    # Comments
    "# comment\n", "#\n",
    # String interpolation
    ~s(${x}), ~s(${x + 1}),
    # Whitespace
    " ", "\t", "\n", "\r",
    # Edge cases
    "", "\\", "\x00", "\xFF"
  ]

  @iterations System.get_env("FUZZ_ITERATIONS", "100000") |> String.to_integer()

  test "lexer never crashes on random byte sequences" do
    for _ <- 1..div(@iterations, 2) do
      input = random_bytes(:rand.uniform(4096))
      assert_no_crash(input)
    end
  end

  test "lexer never crashes on fragment-based inputs" do
    for _ <- 1..div(@iterations, 2) do
      input = random_fragments(:rand.uniform(4096))
      assert_no_crash(input)
    end
  end

  test "lexer handles all single-byte inputs" do
    for byte <- 0..255 do
      input = <<byte>>
      assert_no_crash(input)
    end
  end

  test "lexer handles repeated edge-case characters" do
    edge_cases = [
      String.duplicate("\"", 100),
      String.duplicate("\\", 100),
      String.duplicate("\n", 100),
      String.duplicate(":", 100),
      String.duplicate(".", 100),
      String.duplicate("#", 100),
      String.duplicate("${", 50),
      String.duplicate("0x", 50),
      String.duplicate("0b", 50),
      String.duplicate("0o", 50),
      String.duplicate(~s("""), 33),
      String.duplicate("r\"", 50),
    ]

    for input <- edge_cases do
      assert_no_crash(input)
    end
  end

  # -- Helpers --

  defp assert_no_crash(input) when is_binary(input) do
    result = Phronesis.Lexer.tokenize(input)

    case result do
      {:ok, tokens} when is_list(tokens) ->
        # Walk every token to ensure it is well-formed
        Enum.each(tokens, fn {type, _value, _line, _col} ->
          assert is_atom(type)
        end)

      {:error, {:lexer_error, msg, line, col}} ->
        # Errors are expected for invalid input
        assert is_binary(msg)
        assert is_integer(line)
        assert is_integer(col)

      other ->
        flunk("Unexpected return value from tokenize/1: #{inspect(other)}")
    end
  end

  defp random_bytes(max_len) do
    len = :rand.uniform(max_len + 1) - 1
    :crypto.strong_rand_bytes(len)
  end

  defp random_fragments(max_len) do
    build_fragments(<<>>, max_len)
  end

  defp build_fragments(acc, max_len) when byte_size(acc) >= max_len, do: acc
  defp build_fragments(acc, max_len) do
    fragment = Enum.random(@fragments)
    build_fragments(acc <> fragment, max_len)
  end
end
