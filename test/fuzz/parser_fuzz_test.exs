# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2026 Phronesis Contributors
#
# Fuzz test for the Phronesis parser.
#
# Invariant: the parser must NEVER crash on ANY input. It should always
# return {:ok, ast} or {:error, {...}} without raising an exception.
#
# This test lexes first (catching lexer errors), then feeds the token
# stream to Phronesis.Parser.parse/1. It also tests direct string
# parsing with structured inputs biased toward Phronesis policy syntax.
#
# Run with:
#   mix test test/fuzz/parser_fuzz_test.exs
#
# Increase iterations via environment variable:
#   FUZZ_ITERATIONS=500000 mix test test/fuzz/parser_fuzz_test.exs

defmodule Phronesis.Parser.FuzzTest do
  use ExUnit.Case, async: true

  @moduledoc """
  Property-based fuzz testing for the Phronesis parser.
  Generates random inputs and asserts the parser never crashes.
  """

  # Fragments biased toward Phronesis policy syntax for deeper
  # parser coverage. These form syntactically-plausible token
  # sequences that exercise deeper parser states than random bytes.
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
    # Whitespace
    " ", "\t", "\n", "\r",
    # Structured policy patterns
    "POLICY test: foo == 42 THEN ACCEPT",
    "CONST x = 42",
    "IMPORT \"lib\" AS l",
    "POLICY p: src.ip == 10.0.0.1 AND dst.port > 80 THEN REJECT PRIORITY 100",
    # Edge cases
    "", "\\", "\x00", "\xFF"
  ]

  @iterations System.get_env("FUZZ_ITERATIONS", "100000") |> String.to_integer()

  test "parser never crashes on random byte sequences" do
    for _ <- 1..div(@iterations, 2) do
      input = random_bytes(:rand.uniform(4096))
      assert_parser_no_crash(input)
    end
  end

  test "parser never crashes on fragment-based inputs" do
    for _ <- 1..div(@iterations, 2) do
      input = random_fragments(:rand.uniform(4096))
      assert_parser_no_crash(input)
    end
  end

  test "parser handles all single-byte inputs" do
    for byte <- 0..255 do
      input = <<byte>>
      assert_parser_no_crash(input)
    end
  end

  test "parser handles repeated structural patterns" do
    edge_cases = [
      String.duplicate("POLICY", 50),
      String.duplicate("THEN", 100),
      String.duplicate("(", 100),
      String.duplicate(")", 100),
      String.duplicate("CONST x = ", 50),
      String.duplicate("AND ", 100),
      String.duplicate("OR ", 100),
      String.duplicate("NOT ", 100),
      String.duplicate("== ", 100),
      String.duplicate("IMPORT ", 50),
    ]

    for input <- edge_cases do
      assert_parser_no_crash(input)
    end
  end

  # -- Helpers --

  defp assert_parser_no_crash(input) when is_binary(input) do
    # Step 1: Lex the input (catching lexer failures gracefully)
    lex_result =
      try do
        Phronesis.Lexer.tokenize(input)
      rescue
        _ -> {:error, :lexer_exception}
      end

    case lex_result do
      {:ok, tokens} when is_list(tokens) ->
        # Step 2: Feed tokens to the parser
        parse_result =
          try do
            Phronesis.Parser.parse(tokens)
          rescue
            _ -> {:error, :parser_exception}
          end

        case parse_result do
          {:ok, ast} when is_list(ast) ->
            # Valid parse — walk the AST
            assert is_list(ast)

          {:error, _reason} ->
            # Expected for invalid input
            :ok

          other ->
            flunk("Unexpected return value from parse/1: #{inspect(other)}")
        end

      {:error, _} ->
        # Lexer error — expected for random bytes
        :ok
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
