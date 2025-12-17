# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Lexer do
  @moduledoc """
  Lexer for the Phronesis policy language (v0.2.x).

  Converts source code into a stream of tokens. The lexer handles:

  ## Keywords (15 total)
  POLICY, THEN, AND, OR, NOT, ACCEPT, REJECT, REPORT, EXECUTE,
  IF, ELSE, CONST, IMPORT, AS, PRIORITY

  ## Literals
  - Integers: 42, -17
  - Hex integers: 0xFF, 0xDEADBEEF (v0.2.x)
  - Binary integers: 0b1010, 0b11110000 (v0.2.x)
  - Octal integers: 0o755, 0o777 (v0.2.x)
  - Floats: 3.14, 1.5e10 (scientific notation v0.2.x)
  - Strings: "hello", "multi\\nline"
  - Raw strings: r"no\\escapes" (v0.2.x)
  - Multi-line strings: \"""...\""" (v0.2.x)
  - IPv4 addresses: 192.168.1.1, 10.0.0.0/8
  - IPv6 addresses: 2001:db8::1, ::1, fe80::/10 (v0.2.x)
  - DateTimes: 2025-01-15T10:30:00Z

  ## Operators
  ==, !=, >, >=, <, <=, +, -, *, /, %
  ?. (optional chaining v0.2.x), ?? (null coalescing v0.2.x)

  ## Example

      iex> Phronesis.Lexer.tokenize("CONST x = 0xFF")
      {:ok, [
        {:const, "CONST", 1, 1},
        {:identifier, "x", 1, 7},
        {:assign, "=", 1, 9},
        {:hex_integer, 255, 1, 11},
        {:eof, nil, 1, 15}
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

  # Multi-line strings (""")
  defp tokenize(<<?", ?", ?", rest::binary>>, line, col, acc) do
    case scan_multiline_string(rest, line, col + 3, []) do
      {:ok, value, rest, new_line, new_col} ->
        tokenize(rest, new_line, new_col, [Token.new(:multiline_string, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  # Raw strings (r"...")
  defp tokenize(<<"r\"", rest::binary>>, line, col, acc) do
    case scan_raw_string(rest, line, col + 2, []) do
      {:ok, value, rest, new_line, new_col} ->
        tokenize(rest, new_line, new_col, [Token.new(:raw_string, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
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

  # Optional chaining (v0.2.x)
  defp tokenize(<<"?.", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 2, [Token.new(:question_dot, "?.", line, col) | acc])
  end

  # Null coalescing (v0.2.x)
  defp tokenize(<<"??", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 2, [Token.new(:double_question, "??", line, col) | acc])
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

  # Modulo operator (v0.2.x)
  defp tokenize(<<"%", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:percent, "%", line, col) | acc])
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

  defp tokenize(<<"[", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:lbracket, "[", line, col) | acc])
  end

  defp tokenize(<<"]", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:rbracket, "]", line, col) | acc])
  end

  defp tokenize(<<"{", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:lbrace, "{", line, col) | acc])
  end

  defp tokenize(<<"}", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:rbrace, "}", line, col) | acc])
  end

  defp tokenize(<<",", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:comma, ",", line, col) | acc])
  end

  # IPv6 addresses starting with :: (like ::1, ::ffff:192.168.1.1)
  defp tokenize(<<"::", rest::binary>>, line, col, acc) do
    case scan_ipv6_after_double_colon(rest, ["::"]) do
      {:ok, value, rest, len} ->
        tokenize(rest, line, col + len, [Token.new(:ipv6_address, value, line, col) | acc])

      :not_ipv6 ->
        # It's just two colons, emit them separately
        tokenize(rest, line, col + 2, [Token.new(:colon, ":", line, col + 1), Token.new(:colon, ":", line, col) | acc])
    end
  end

  defp tokenize(<<":", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:colon, ":", line, col) | acc])
  end

  defp tokenize(<<".", rest::binary>>, line, col, acc) do
    tokenize(rest, line, col + 1, [Token.new(:dot, ".", line, col) | acc])
  end

  # String literals (check for interpolation)
  defp tokenize(<<"\"", rest::binary>>, line, col, acc) do
    case scan_string_or_interpolated(rest, line, col + 1, [], false) do
      {:ok, :string, value, rest, new_line, new_col} ->
        tokenize(rest, new_line, new_col, [Token.new(:string, value, line, col) | acc])

      {:ok, :interpolated, parts, rest, new_line, new_col} ->
        tokenize(rest, new_line, new_col, [Token.new(:interpolated_string, parts, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  # Hex integers (0x...) - must be before regular numbers
  defp tokenize(<<"0x", rest::binary>>, line, col, acc) do
    case scan_hex(rest, []) do
      {:ok, value, rest, len} ->
        tokenize(rest, line, col + 2 + len, [Token.new(:hex_integer, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  defp tokenize(<<"0X", rest::binary>>, line, col, acc) do
    case scan_hex(rest, []) do
      {:ok, value, rest, len} ->
        tokenize(rest, line, col + 2 + len, [Token.new(:hex_integer, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  # Binary integers (0b...)
  defp tokenize(<<"0b", rest::binary>>, line, col, acc) do
    case scan_binary(rest, []) do
      {:ok, value, rest, len} ->
        tokenize(rest, line, col + 2 + len, [Token.new(:binary_integer, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  defp tokenize(<<"0B", rest::binary>>, line, col, acc) do
    case scan_binary(rest, []) do
      {:ok, value, rest, len} ->
        tokenize(rest, line, col + 2 + len, [Token.new(:binary_integer, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  # Octal integers (0o...)
  defp tokenize(<<"0o", rest::binary>>, line, col, acc) do
    case scan_octal(rest, []) do
      {:ok, value, rest, len} ->
        tokenize(rest, line, col + 2 + len, [Token.new(:octal_integer, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  defp tokenize(<<"0O", rest::binary>>, line, col, acc) do
    case scan_octal(rest, []) do
      {:ok, value, rest, len} ->
        tokenize(rest, line, col + 2 + len, [Token.new(:octal_integer, value, line, col) | acc])

      {:error, msg} ->
        {:error, {:lexer_error, msg, line, col}}
    end
  end

  # Numbers (integers, floats, IP addresses, datetimes)
  defp tokenize(<<c, _::binary>> = source, line, col, acc) when c in ?0..?9 do
    {value, rest, len} = scan_number(source, [])

    case parse_number_or_ip(value) do
      {:integer, n} ->
        tokenize(rest, line, col + len, [Token.new(:integer, n, line, col) | acc])

      {:float, n} ->
        tokenize(rest, line, col + len, [Token.new(:float, n, line, col) | acc])

      {:ip_address, ip} ->
        tokenize(rest, line, col + len, [Token.new(:ip_address, ip, line, col) | acc])

      {:ipv6_address, ip} ->
        tokenize(rest, line, col + len, [Token.new(:ipv6_address, ip, line, col) | acc])

      {:datetime, dt} ->
        tokenize(rest, line, col + len, [Token.new(:datetime, dt, line, col) | acc])
    end
  end

  # Identifiers and keywords (with IPv6 detection for hex-starting addresses)
  defp tokenize(<<c, _::binary>> = source, line, col, acc)
       when c in ?a..?z or c in ?A..?Z or c == ?_ do
    {word, rest, len} = scan_identifier(source, [])

    # Check if this could be start of an IPv6 address (hex chars followed by :)
    if is_hex_string?(word) and String.match?(rest, ~r/^::?/) do
      case try_scan_ipv6(word, rest) do
        {:ok, ipv6, rest2, total_len} ->
          tokenize(rest2, line, col + total_len, [Token.new(:ipv6_address, ipv6, line, col) | acc])

        :not_ipv6 ->
          type = Token.lookup_keyword(word)
          tokenize(rest, line, col + len, [Token.new(type, word, line, col) | acc])
      end
    else
      type = Token.lookup_keyword(word)
      tokenize(rest, line, col + len, [Token.new(type, word, line, col) | acc])
    end
  end

  # Unknown character
  defp tokenize(<<c, _::binary>>, line, col, _acc) do
    {:error, {:lexer_error, "unexpected character: #{<<c>>}", line, col}}
  end

  # ============================================================
  # Helper Functions
  # ============================================================

  # Skip to end of line
  defp skip_to_newline(<<?\n, _::binary>> = rest), do: {:ok, rest}
  defp skip_to_newline(<<_, rest::binary>>), do: skip_to_newline(rest)
  defp skip_to_newline(""), do: {:ok, ""}

  # Scan a string, detecting if it has interpolations
  # has_interpolation tracks if we've seen ${
  defp scan_string_or_interpolated(<<"\"", rest::binary>>, line, col, acc, false) do
    # No interpolation, return regular string
    {:ok, :string, IO.iodata_to_binary(Enum.reverse(acc)), rest, line, col + 1}
  end

  defp scan_string_or_interpolated(<<"\"", rest::binary>>, line, col, acc, true) do
    # Has interpolation, finalize and return parts
    parts = finalize_interpolated_parts(acc)
    {:ok, :interpolated, parts, rest, line, col + 1}
  end

  # Detect interpolation start ${ when not yet interpolating (acc is charlist)
  defp scan_string_or_interpolated(<<"${", rest::binary>>, line, col, acc, false) do
    case scan_interpolation_expr(rest, line, col + 2, [], 0) do
      {:ok, expr_tokens, rest2, new_line, new_col} ->
        current_str = IO.iodata_to_binary(Enum.reverse(acc))
        new_acc = [{:expr, expr_tokens}, {:str, current_str}]
        scan_string_or_interpolated(rest2, new_line, new_col, new_acc, true)

      {:error, msg} ->
        {:error, msg}
    end
  end

  # Detect interpolation start ${ when already interpolating (acc has parts)
  defp scan_string_or_interpolated(<<"${", rest::binary>>, line, col, acc, true) do
    case scan_interpolation_expr(rest, line, col + 2, [], 0) do
      {:ok, expr_tokens, rest2, new_line, new_col} ->
        # Finalize any in-progress string building
        finalized_acc =
          case acc do
            [{:str_building, chars} | rest_acc] ->
              str = IO.iodata_to_binary(Enum.reverse(chars))
              [{:str, str} | rest_acc]

            _ ->
              acc
          end

        new_acc = [{:expr, expr_tokens} | finalized_acc]
        scan_string_or_interpolated(rest2, new_line, new_col, new_acc, true)

      {:error, msg} ->
        {:error, msg}
    end
  end

  # Handle adding to accumulator when we already have interpolation parts
  defp scan_string_or_interpolated(<<c, rest::binary>>, line, col, [{:expr, _} | _] = acc, true)
       when c != ?" do
    # Start new string part after expression
    {char, new_line, new_col} = process_string_char(c, rest, line, col)
    scan_string_or_interpolated(rest, new_line, new_col, [{:str_building, [char]} | acc], true)
  end

  defp scan_string_or_interpolated(<<c, rest::binary>>, line, col, [{:str_building, chars} | rest_acc], true)
       when c != ?" do
    {char, new_line, new_col} = process_string_char(c, rest, line, col)
    scan_string_or_interpolated(rest, new_line, new_col, [{:str_building, [char | chars]} | rest_acc], true)
  end

  # Escape sequences
  defp scan_string_or_interpolated(<<"\\n", rest::binary>>, line, col, acc, has_interp) do
    add_char_to_acc(?\n, rest, line, col + 2, acc, has_interp)
  end

  defp scan_string_or_interpolated(<<"\\t", rest::binary>>, line, col, acc, has_interp) do
    add_char_to_acc(?\t, rest, line, col + 2, acc, has_interp)
  end

  defp scan_string_or_interpolated(<<"\\r", rest::binary>>, line, col, acc, has_interp) do
    add_char_to_acc(?\r, rest, line, col + 2, acc, has_interp)
  end

  defp scan_string_or_interpolated(<<"\\\"", rest::binary>>, line, col, acc, has_interp) do
    add_char_to_acc(?", rest, line, col + 2, acc, has_interp)
  end

  defp scan_string_or_interpolated(<<"\\\\", rest::binary>>, line, col, acc, has_interp) do
    add_char_to_acc(?\\, rest, line, col + 2, acc, has_interp)
  end

  defp scan_string_or_interpolated(<<"\\$", rest::binary>>, line, col, acc, has_interp) do
    # Escape $ to avoid interpolation
    add_char_to_acc(?$, rest, line, col + 2, acc, has_interp)
  end

  defp scan_string_or_interpolated(<<?\n, rest::binary>>, line, _col, acc, has_interp) do
    add_char_to_acc(?\n, rest, line + 1, 1, acc, has_interp)
  end

  defp scan_string_or_interpolated(<<c, rest::binary>>, line, col, acc, has_interp) do
    add_char_to_acc(c, rest, line, col + 1, acc, has_interp)
  end

  defp scan_string_or_interpolated("", _line, _col, _acc, _has_interp) do
    {:error, "unterminated string"}
  end

  # Helper to add a character to the appropriate accumulator
  defp add_char_to_acc(char, rest, line, col, acc, false) do
    scan_string_or_interpolated(rest, line, col, [char | acc], false)
  end

  defp add_char_to_acc(char, rest, line, col, [{:str_building, chars} | rest_acc], true) do
    scan_string_or_interpolated(rest, line, col, [{:str_building, [char | chars]} | rest_acc], true)
  end

  defp add_char_to_acc(char, rest, line, col, [{:expr, _} | _] = acc, true) do
    scan_string_or_interpolated(rest, line, col, [{:str_building, [char]} | acc], true)
  end

  defp add_char_to_acc(char, rest, line, col, [{:str, _} | _] = acc, true) do
    scan_string_or_interpolated(rest, line, col, [{:str_building, [char]} | acc], true)
  end

  defp process_string_char(?\n, _rest, line, _col), do: {?\n, line + 1, 1}
  defp process_string_char(c, _rest, line, col), do: {c, line, col + 1}

  # Scan expression inside ${...}
  defp scan_interpolation_expr(<<"}", rest::binary>>, line, col, acc, 0) do
    # End of interpolation
    expr_str = IO.iodata_to_binary(Enum.reverse(acc))
    case tokenize(expr_str) do
      {:ok, tokens} ->
        # Remove the EOF token
        expr_tokens = Enum.reject(tokens, fn {type, _, _, _} -> type == :eof end)
        {:ok, expr_tokens, rest, line, col + 1}

      {:error, _} = err ->
        err
    end
  end

  defp scan_interpolation_expr(<<"{", rest::binary>>, line, col, acc, depth) do
    # Nested brace
    scan_interpolation_expr(rest, line, col + 1, [?{ | acc], depth + 1)
  end

  defp scan_interpolation_expr(<<"}", rest::binary>>, line, col, acc, depth) when depth > 0 do
    # Closing nested brace
    scan_interpolation_expr(rest, line, col + 1, [?} | acc], depth - 1)
  end

  defp scan_interpolation_expr(<<c, rest::binary>>, line, col, acc, depth) do
    new_line = if c == ?\n, do: line + 1, else: line
    new_col = if c == ?\n, do: 1, else: col + 1
    scan_interpolation_expr(rest, new_line, new_col, [c | acc], depth)
  end

  defp scan_interpolation_expr("", _line, _col, _acc, _depth) do
    {:error, "unterminated interpolation"}
  end

  # Finalize interpolated string parts
  defp finalize_interpolated_parts(acc) do
    acc
    |> Enum.reverse()
    |> Enum.map(fn
      {:str, s} -> {:string, s}
      {:str_building, chars} -> {:string, IO.iodata_to_binary(Enum.reverse(chars))}
      {:expr, tokens} -> {:expr, tokens}
    end)
    |> Enum.reject(fn
      {:string, ""} -> true
      _ -> false
    end)
  end

  # Scan a raw string (no escape sequences)
  defp scan_raw_string(<<"\"", rest::binary>>, line, col, acc) do
    {:ok, IO.iodata_to_binary(Enum.reverse(acc)), rest, line, col + 1}
  end

  defp scan_raw_string(<<?\n, rest::binary>>, line, _col, acc) do
    scan_raw_string(rest, line + 1, 1, [?\n | acc])
  end

  defp scan_raw_string(<<c, rest::binary>>, line, col, acc) do
    scan_raw_string(rest, line, col + 1, [c | acc])
  end

  defp scan_raw_string("", _line, _col, _acc) do
    {:error, "unterminated raw string"}
  end

  # Scan a multi-line string (""")
  defp scan_multiline_string(<<?", ?", ?", rest::binary>>, line, col, acc) do
    {:ok, IO.iodata_to_binary(Enum.reverse(acc)), rest, line, col + 3}
  end

  defp scan_multiline_string(<<?\n, rest::binary>>, line, _col, acc) do
    scan_multiline_string(rest, line + 1, 1, [?\n | acc])
  end

  defp scan_multiline_string(<<c, rest::binary>>, line, col, acc) do
    scan_multiline_string(rest, line, col + 1, [c | acc])
  end

  defp scan_multiline_string("", _line, _col, _acc) do
    {:error, "unterminated multi-line string"}
  end

  # Scan hex digits
  defp scan_hex(<<c, rest::binary>>, acc) when c in ?0..?9 or c in ?a..?f or c in ?A..?F do
    scan_hex(rest, [c | acc])
  end

  defp scan_hex(<<c, _::binary>>, []) when c in ?g..?z or c in ?G..?Z do
    {:error, "invalid hex digit"}
  end

  defp scan_hex(_rest, []) do
    {:error, "expected hex digits after 0x"}
  end

  defp scan_hex(rest, acc) do
    str = IO.iodata_to_binary(Enum.reverse(acc))
    {:ok, String.to_integer(str, 16), rest, String.length(str)}
  end

  # Scan binary digits
  defp scan_binary(<<c, rest::binary>>, acc) when c in [?0, ?1] do
    scan_binary(rest, [c | acc])
  end

  defp scan_binary(<<c, _::binary>>, []) when c in ?2..?9 do
    {:error, "invalid binary digit"}
  end

  defp scan_binary(_rest, []) do
    {:error, "expected binary digits after 0b"}
  end

  defp scan_binary(rest, acc) do
    str = IO.iodata_to_binary(Enum.reverse(acc))
    {:ok, String.to_integer(str, 2), rest, String.length(str)}
  end

  # Scan octal digits
  defp scan_octal(<<c, rest::binary>>, acc) when c in ?0..?7 do
    scan_octal(rest, [c | acc])
  end

  defp scan_octal(<<c, _::binary>>, []) when c in ?8..?9 do
    {:error, "invalid octal digit"}
  end

  defp scan_octal(_rest, []) do
    {:error, "expected octal digits after 0o"}
  end

  defp scan_octal(rest, acc) do
    str = IO.iodata_to_binary(Enum.reverse(acc))
    {:ok, String.to_integer(str, 8), rest, String.length(str)}
  end

  # Scan a number/IP/datetime/IPv6 (extended for scientific notation and IPv6)
  defp scan_number(<<c, rest::binary>>, acc)
       when c in ?0..?9 or c == ?. or c == ?/ or c == ?- or c == ?: or
              c == ?T or c == ?Z or c == ?e or c == ?E or c == ?+ or
              c in ?a..?f or c in ?A..?F do
    scan_number(rest, [c | acc])
  end

  defp scan_number(rest, acc) do
    value = IO.iodata_to_binary(Enum.reverse(acc))
    {value, rest, String.length(value)}
  end

  # Parse number, IP address, datetime, or scientific notation
  defp parse_number_or_ip(value) do
    cond do
      # DateTime: 2025-12-16T10:30:00Z
      String.match?(value, ~r/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$/) ->
        {:datetime, value}

      # Check for IPv6 (contains : and validates as IPv6)
      String.contains?(value, ":") and valid_ipv6_address?(value) ->
        {:ipv6_address, value}

      # IP with CIDR: 192.168.1.0/24
      String.match?(value, ~r/^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\/\d{1,2}$/) ->
        {:ip_address, value}

      # IP address: 192.168.1.1
      String.match?(value, ~r/^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/) ->
        {:ip_address, value}

      # Scientific notation float: 1.5e10, 3e-5
      String.match?(value, ~r/^-?\d+\.?\d*[eE][+-]?\d+$/) ->
        {:float, parse_scientific(value)}

      # Float: 3.14
      String.contains?(value, ".") and String.match?(value, ~r/^\d+\.\d+$/) ->
        {:float, String.to_float(value)}

      # Integer (only digits)
      String.match?(value, ~r/^\d+$/) ->
        {:integer, String.to_integer(value)}

      # Fallback - could be malformed, treat as integer if possible
      true ->
        try do
          {:integer, String.to_integer(value)}
        rescue
          _ -> {:ipv6_address, value}  # Last resort - assume IPv6-like
        end
    end
  end

  # Parse scientific notation
  defp parse_scientific(value) do
    case Float.parse(value) do
      {float, ""} -> float
      {float, _} -> float
      :error -> 0.0
    end
  end

  # Scan an identifier
  defp scan_identifier(<<c, rest::binary>>, acc)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ do
    scan_identifier(rest, [c | acc])
  end

  defp scan_identifier(rest, acc) do
    word = IO.iodata_to_binary(Enum.reverse(acc))
    {word, rest, String.length(word)}
  end

  # ============================================================
  # IPv6 Scanning Helpers (v0.2.x)
  # ============================================================

  # Check if a string contains only hex characters (potential IPv6 start)
  defp is_hex_string?(str) do
    String.match?(str, ~r/^[0-9a-fA-F]+$/)
  end

  # Try to scan a complete IPv6 address starting with a hex identifier
  # Called when we've scanned something like "fe80" and see ":"
  defp try_scan_ipv6(prefix, rest) do
    {more, rest2, len} = scan_ipv6_continuation(rest, [])

    if more == "" do
      :not_ipv6
    else
      full = prefix <> more

      if valid_ipv6_address?(full) do
        {:ok, full, rest2, String.length(prefix) + len}
      else
        :not_ipv6
      end
    end
  end

  # Scan the continuation of an IPv6 address after the first group
  defp scan_ipv6_continuation(<<c, rest::binary>>, acc)
       when c in ?0..?9 or c in ?a..?f or c in ?A..?F or c == ?: or c == ?. or c == ?/ do
    scan_ipv6_continuation(rest, [c | acc])
  end

  defp scan_ipv6_continuation(rest, acc) do
    value = IO.iodata_to_binary(Enum.reverse(acc))
    {value, rest, String.length(value)}
  end

  # Validate a complete IPv6 address
  defp valid_ipv6_address?(addr) do
    # Remove CIDR suffix for validation
    {base, _cidr} =
      case String.split(addr, "/", parts: 2) do
        [base, cidr] -> {base, cidr}
        [base] -> {base, nil}
      end

    cond do
      # Full form: 8 groups of hex separated by colons
      String.match?(base, ~r/^[0-9a-fA-F]{1,4}(:[0-9a-fA-F]{1,4}){7}$/) ->
        true

      # Compressed with :: - must have at least one ::
      String.contains?(base, "::") ->
        # Count groups on each side of ::
        parts = String.split(base, "::", parts: 2)
        length(parts) == 2 and valid_ipv6_compressed?(parts)

      # IPv4-mapped without ::
      String.match?(base, ~r/^[0-9a-fA-F]{1,4}(:[0-9a-fA-F]{1,4}){5}:\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/) ->
        true

      true ->
        false
    end
  end

  # Validate compressed IPv6 (parts split on ::)
  defp valid_ipv6_compressed?([left, right]) do
    left_groups = if left == "", do: [], else: String.split(left, ":")
    right_groups = if right == "", do: [], else: String.split(right, ":")

    # Total groups must be <= 7 (:: represents at least one group)
    total_groups = length(left_groups) + length(right_groups)

    if total_groups <= 7 do
      # Validate each group is valid hex (1-4 chars) or IPv4 for last group
      all_valid_groups?(left_groups) and all_valid_groups_or_ipv4?(right_groups)
    else
      false
    end
  end

  defp all_valid_groups?(groups) do
    Enum.all?(groups, fn g ->
      String.match?(g, ~r/^[0-9a-fA-F]{1,4}$/)
    end)
  end

  defp all_valid_groups_or_ipv4?(groups) do
    case groups do
      [] ->
        true

      groups ->
        {maybe_ipv4, rest} = List.pop_at(groups, -1)

        rest_valid = Enum.all?(rest, fn g -> String.match?(g, ~r/^[0-9a-fA-F]{1,4}$/) end)

        last_valid =
          String.match?(maybe_ipv4, ~r/^[0-9a-fA-F]{1,4}$/) or
            String.match?(maybe_ipv4, ~r/^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/)

        rest_valid and last_valid
    end
  end

  # Scan IPv6 address after we've seen "::"
  # Handles: ::1, ::ffff:192.168.1.1, ::/128, etc.
  defp scan_ipv6_after_double_colon(<<c, _::binary>> = source, acc) when c in ?0..?9 or c in ?a..?f or c in ?A..?F do
    {rest_addr, rest, len} = scan_ipv6_chars(source, [])
    full_addr = IO.iodata_to_binary(Enum.reverse(acc)) <> rest_addr

    if valid_ipv6_address?(full_addr) do
      {:ok, full_addr, rest, 2 + len}
    else
      :not_ipv6
    end
  end

  defp scan_ipv6_after_double_colon(_rest, _acc) do
    :not_ipv6
  end

  # Scan characters that can be part of an IPv6 address (hex, :, ., /)
  defp scan_ipv6_chars(<<c, rest::binary>>, acc)
       when c in ?0..?9 or c in ?a..?f or c in ?A..?F or c == ?: or c == ?. or c == ?/ do
    scan_ipv6_chars(rest, [c | acc])
  end

  defp scan_ipv6_chars(rest, acc) do
    value = IO.iodata_to_binary(Enum.reverse(acc))
    {value, rest, String.length(value)}
  end
end
