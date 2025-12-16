# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Lexer do
  @moduledoc """
  Lexer for the Phronesis policy language.

  Converts source code into a stream of tokens. The lexer handles:

  - Keywords (15 total): POLICY, THEN, AND, OR, etc.
  - Literals: integers, floats, strings, IP addresses, datetimes
  - Operators: ==, !=, >, >=, <, <=, +, -, *, /
  - Delimiters: (, ), ,, :, .
  - Identifiers: alphanumeric with underscores
  - Comments: lines starting with #

  ## Example

      iex> Phronesis.Lexer.tokenize("CONST x = 42")
      {:ok, [
        {:const, "CONST", 1, 1},
        {:identifier, "x", 1, 7},
        {:assign, "=", 1, 9},
        {:integer, 42, 1, 11},
        {:eof, nil, 1, 13}
      ]}
  """

  alias Phronesis.Token

  @type error :: {:error, {:lexer_error, String.t(), pos_integer(), pos_integer()}}

  @whitespace [?\s, ?\t, ?\r]

  @doc """
  Tokenize source code into a list of tokens.
  """
  @spec tokenize(String.t()) :: {:ok, [Token.t()]} | error()
  def tokenize(source) when is_binary(source) do
    tokenize(source, 1, 1, [])
  end

  # End of input
  defp tokenize("", line, col, acc) do
    tokens = Enum.reverse([Token.new(:eof, nil, line, col) | acc])
    {:ok, tokens}
  end

  # Skip whitespace
  defp tokenize(<<c, rest::binary>>, line, col, acc) when c in @whitespace do
    tokenize(rest, line, col + 1, acc)
  end

  # Newlines
  defp tokenize(<<?\n, rest::binary>>, line, _col, acc) do
    tokenize(rest, line + 1, 1, acc)
  end

  # Comments (# to end of line)
  defp tokenize(<<"#", rest::binary>>, line, col, acc) do
    {_, rest} = skip_to_newline(rest)
    tokenize(rest, line, col, acc)
  end

  # Multi-character operators
  defp tokenize(<<"==", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 2, [Token.new(:eq, "==", line, col) | acc])
  end

  defp tokenize(<<"!=", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 2, [Token.new(:neq, "!=", line, col) | acc])
  end

  defp tokenize(<<">=", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 2, [Token.new(:gte, ">=", line, col) | acc])
  end

  defp tokenize(<<"<=", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 2, [Token.new(:lte, "<=", line, col) | acc])
  end

  # Single-character operators
  defp tokenize(<<">", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:gt, ">", line, col) | acc])
  end

  defp tokenize(<<"<", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:lt, "<", line, col) | acc])
  end

  defp tokenize(<<"+", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:plus, "+", line, col) | acc])
  end

  defp tokenize(<<"-", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:minus, "-", line, col) | acc])
  end

  defp tokenize(<<"*", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:star, "*", line, col) | acc])
  end

  defp tokenize(<<"/", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:slash, "/", line, col) | acc])
  end

  defp tokenize(<<"=", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:assign, "=", line, col) | acc])
  end

  # Delimiters
  defp tokenize(<<"(", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:lparen, "(", line, col) | acc])
  end

  defp tokenize(<<")", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:rparen, ")", line, col) | acc])
  end

  defp tokenize(<<",", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:comma, ",", line, col) | acc])
  end

  defp tokenize(<<":", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:colon, ":", line, col) | acc])
  end

  defp tokenize(<<".", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:dot, ".", line, col) | acc])
  end

  # String literals
  defp tokenize(<<"\"", rest::binary>>, line, col, acc) do
    case scan_string(rest, line, col + 1, []) do
      {:ok, value, rest, new_line, new_col} ->
        tokenize(rest, new_line, new_col, [Token.new(:string, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  # Numbers (integers, floats, IP addresses)
  defp tokenize(<<c, _::binary>> = source, line, col, acc) when c in ?0..?9 do
    {value, rest, len} = scan_number(source, [])

    case parse_number_or_ip(value) do
      {:integer, n} ->
        tokenize(rest, line, col + len, [Token.new(:integer, n, line, col) | acc])

      {:float, n} ->
        tokenize(rest, line, col + len, [Token.new(:float, n, line, col) | acc])

      {:ip_address, ip} ->
        tokenize(rest, line, col + len, [Token.new(:ip_address, ip, line, col) | acc])

      {:datetime, dt} ->
        tokenize(rest, line, col + len, [Token.new(:datetime, dt, line, col) | acc])
    end
  end

  # Identifiers and keywords
  defp tokenize(<<c, _::binary>> = source, line, col, acc)
       when c in ?a..?z or c in ?A..?Z or c == ?_ do
    {word, rest, len} = scan_identifier(source, [])
    type = Token.lookup_keyword(word)
    tokenize(rest, line, col + len, [Token.new(type, word, line, col) | acc])
  end

  # Unknown character
  defp tokenize(<<c, _::binary>>, line, col, _acc) do
    {:error, {:lexer_error, "unexpected character: #{<<c>>}", line, col}}
  end

  # Helper: skip to end of line
  defp skip_to_newline(<<?\n, _::binary>> = rest), do: {:ok, rest}
  defp skip_to_newline(<<_, rest::binary>>), do: skip_to_newline(rest)
  defp skip_to_newline(""), do: {:ok, ""}

  # Helper: scan a string literal
  defp scan_string(<<"\"", rest::binary>>, line, col, acc) do
    {:ok, IO.iodata_to_binary(Enum.reverse(acc)), rest, line, col + 1}
  end

  defp scan_string(<<"\\n", rest::binary>>, line, col, acc) do
    scan_string(rest, line, col + 2, [?\n | acc])
  end

  defp scan_string(<<"\\t", rest::binary>>, line, col, acc) do
    scan_string(rest, line, col + 2, [?\t | acc])
  end

  defp scan_string(<<"\\\"", rest::binary>>, line, col, acc) do
    scan_string(rest, line, col + 2, [?" | acc])
  end

  defp scan_string(<<"\\\\", rest::binary>>, line, col, acc) do
    scan_string(rest, line, col + 2, [?\\ | acc])
  end

  defp scan_string(<<?\n, rest::binary>>, line, _col, acc) do
    scan_string(rest, line + 1, 1, [?\n | acc])
  end

  defp scan_string(<<c, rest::binary>>, line, col, acc) do
    scan_string(rest, line, col + 1, [c | acc])
  end

  defp scan_string("", _line, _col, _acc) do
    {:error, "unterminated string"}
  end

  # Helper: scan a number/IP/datetime
  defp scan_number(<<c, rest::binary>>, acc)
       when c in ?0..?9 or c == ?. or c == ?/ or c == ?- or c == ?: or c == ?T or c == ?Z do
    scan_number(rest, [c | acc])
  end

  defp scan_number(rest, acc) do
    value = IO.iodata_to_binary(Enum.reverse(acc))
    {value, rest, String.length(value)}
  end

  # Helper: parse number, IP address, or datetime
  defp parse_number_or_ip(value) do
    cond do
      # DateTime: 2025-12-16T10:30:00Z
      String.match?(value, ~r/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$/) ->
        {:datetime, value}

      # IP with CIDR: 192.168.1.0/24
      String.match?(value, ~r/^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\/\d{1,2}$/) ->
        {:ip_address, value}

      # IP address: 192.168.1.1
      String.match?(value, ~r/^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/) ->
        {:ip_address, value}

      # Float: 3.14
      String.contains?(value, ".") ->
        {:float, String.to_float(value)}

      # Integer
      true ->
        {:integer, String.to_integer(value)}
    end
  end

  # Helper: scan an identifier
  defp scan_identifier(<<c, rest::binary>>, acc)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ do
    scan_identifier(rest, [c | acc])
  end

  defp scan_identifier(rest, acc) do
    word = IO.iodata_to_binary(Enum.reverse(acc))
    {word, rest, String.length(word)}
  end
end
