# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

defmodule Phronesis.IncrementalLexer do
  @moduledoc """
  Incremental lexing support for the Phronesis policy language.

  This module wraps the existing `Phronesis.Lexer` to provide incremental
  re-lexing. When an edit occurs, only the affected token range is re-lexed,
  and the resulting tokens are spliced back into the cached token list.

  All data structures are immutable — functions return a new state rather
  than mutating the old one.

  ## Design

  Follows tree-sitter's approach:

  1. Store the previous token list with byte offsets
  2. On edit, receive an edit delta (start, old_end, new_text)
  3. Find the affected token range
  4. Re-lex only that range plus a small buffer
  5. Splice the new tokens into the cached list

  ## Example

      iex> state = Phronesis.IncrementalLexer.create("CONST x = 42")
      iex> state = Phronesis.IncrementalLexer.edit(state, %{start: 10, old_end: 12, new_text: "99"})
      iex> Phronesis.IncrementalLexer.source(state)
      "CONST x = 99"
  """

  alias Phronesis.Lexer

  @type edit :: %{
    start: non_neg_integer(),
    old_end: non_neg_integer(),
    new_text: String.t()
  }

  @type cached_token :: %{
    token: Phronesis.Token.t(),
    start_offset: non_neg_integer(),
    end_offset: non_neg_integer()
  }

  @type t :: %{
    source: String.t(),
    tokens: [cached_token()]
  }

  @resync_buffer 2

  @doc """
  Create a new incremental lexer from the given source.
  """
  @spec create(String.t()) :: t()
  def create(source) when is_binary(source) do
    tokens = full_lex(source)
    %{source: source, tokens: tokens}
  end

  @doc """
  Apply an edit to the source and re-lex only the affected region.

  Returns a new state with the updated source and tokens.
  """
  @spec edit(t(), edit()) :: t()
  def edit(state, %{start: start, old_end: old_end, new_text: new_text}) do
    old_source = state.source
    size = byte_size(old_source)
    # Clamp the edit window into the source so an out-of-bounds delta (e.g. an old_end
    # past end-of-buffer) can't drive binary_part/3 with a negative length.
    start = start |> max(0) |> min(size)
    old_end = old_end |> max(start) |> min(size)

    # Apply the text edit.
    prefix = binary_part(old_source, 0, start)
    suffix_start = old_end
    suffix_len = byte_size(old_source) - suffix_start
    suffix = binary_part(old_source, suffix_start, suffix_len)
    new_source = prefix <> new_text <> suffix

    new_end = start + byte_size(new_text)
    delta = new_end - old_end
    n = length(state.tokens)

    # Find the first affected token index.
    first_raw = find_first_after(state.tokens, start, 0)
    first_affected0 = max(0, first_raw - @resync_buffer)

    # Find the last affected token: first token starting at or past old_end.
    last_raw = find_last_affected(state.tokens, old_end, first_affected0)
    last_affected = min(n, last_raw + @resync_buffer)

    # Determine byte range to re-lex in the new source.
    relex_start_raw =
      if first_affected0 < n do
        tok = Enum.at(state.tokens, first_affected0)
        min(tok.start_offset, start)
      else
        start
      end

    # Snap the re-lex start back to the beginning of its line. An edit inside a
    # line-structured token (e.g. a comment, which runs to end-of-line and yields no
    # token) would otherwise start the re-lex mid-line and be misread as identifiers.
    relex_start = line_start(new_source, relex_start_raw)

    # Recompute the head boundary so it stays consistent with the snapped start: the
    # head is exactly the tokens that end at or before relex_start.
    first_affected = Enum.count(state.tokens, fn ct -> ct.end_offset <= relex_start end)

    relex_end_old =
      if last_affected > 0 and last_affected <= n do
        tok = Enum.at(state.tokens, last_affected - 1)
        max(tok.end_offset, old_end)
      else
        old_end
      end

    relex_end = min(byte_size(new_source), relex_end_old + delta)

    # Re-lex the affected region.
    region = binary_part(new_source, relex_start, relex_end - relex_start)
    new_tokens_raw = full_lex(region)

    # Offset new tokens and filter out EOF.
    new_tokens =
      new_tokens_raw
      |> Enum.reject(fn ct -> elem(ct.token, 0) == :eof end)
      |> Enum.map(fn ct ->
        %{ct | start_offset: ct.start_offset + relex_start,
               end_offset: ct.end_offset + relex_start}
      end)

    # Build head: tokens before the affected region.
    head = Enum.take(state.tokens, first_affected)

    # Build tail: tokens after the affected region with adjusted offsets.
    tail =
      Enum.drop(state.tokens, last_affected)
      |> Enum.map(fn ct ->
        %{ct | start_offset: ct.start_offset + delta,
               end_offset: ct.end_offset + delta}
      end)

    # Combine and ensure EOF is present.
    combined = head ++ new_tokens ++ tail
    has_eof = Enum.any?(combined, fn ct -> elem(ct.token, 0) == :eof end)

    combined =
      if has_eof do
        combined
      else
        eof_pos = byte_size(new_source)
        combined ++ [%{token: {:eof, nil, 1, eof_pos + 1}, start_offset: eof_pos, end_offset: eof_pos}]
      end

    %{source: new_source, tokens: combined}
  end

  @doc """
  Get all current tokens.
  """
  @spec tokens(t()) :: [cached_token()]
  def tokens(state), do: state.tokens

  @doc """
  Get the current source text.
  """
  @spec source(t()) :: String.t()
  def source(state), do: state.source

  @doc """
  Get token kinds (excluding EOF) for comparison.
  """
  @spec token_types(t()) :: [atom()]
  def token_types(state) do
    state.tokens
    |> Enum.reject(fn ct -> elem(ct.token, 0) == :eof end)
    |> Enum.map(fn ct -> elem(ct.token, 0) end)
  end

  # =========================================================================
  # Internal helpers
  # =========================================================================

  # Perform a full lex and compute byte offsets from column positions.
  #
  # The Phronesis lexer returns tokens as {type, value, line, col} tuples.
  # To get byte offsets, we track position through the source text using
  # the line/column info plus the token's textual representation length.
  @spec full_lex(String.t()) :: [cached_token()]
  defp full_lex(source) do
    case Lexer.tokenize(source) do
      {:ok, tokens} ->
        assign_byte_offsets(tokens, source)

      {:error, _} ->
        # On lex error, return just an EOF token.
        eof_pos = byte_size(source)
        [%{token: {:eof, nil, 1, 1}, start_offset: eof_pos, end_offset: eof_pos}]
    end
  end

  # Assign byte offsets to tokens by mapping line/column to byte positions.
  defp assign_byte_offsets(tokens, source) do
    # Build a line-start-offset table.
    lines = String.split(source, "\n", trim: false)
    line_offsets = build_line_offsets(lines)

    Enum.map(tokens, fn {type, value, line, col} = token ->
      start_offset = line_col_to_offset(line_offsets, line, col)
      token_len = token_byte_length(type, value, source, start_offset)
      end_offset = start_offset + token_len
      %{token: token, start_offset: start_offset, end_offset: end_offset}
    end)
  end

  # Build a map from 1-based line number to byte offset of line start.
  defp build_line_offsets(lines) do
    {offsets, _} =
      Enum.reduce(lines, {%{}, 0}, fn line, {acc, offset} ->
        line_num = map_size(acc) + 1
        {Map.put(acc, line_num, offset), offset + byte_size(line) + 1}
      end)
    offsets
  end

  # Convert 1-based line/column to a 0-based byte offset.
  defp line_col_to_offset(line_offsets, line, col) do
    line_start = Map.get(line_offsets, line, 0)
    line_start + col - 1
  end

  # Estimate the byte length of a token from its type and value.
  defp token_byte_length(:eof, _value, _source, _offset), do: 0
  defp token_byte_length(:string, value, _source, _offset) when is_binary(value),
    do: byte_size(value) + 2  # quotes
  defp token_byte_length(:raw_string, value, _source, _offset) when is_binary(value),
    do: byte_size(value) + 3  # r"..."
  defp token_byte_length(:multiline_string, value, _source, _offset) when is_binary(value),
    do: byte_size(value) + 6  # """..."""
  defp token_byte_length(:integer, value, _source, _offset) when is_integer(value),
    do: byte_size(Integer.to_string(value))
  defp token_byte_length(:hex_integer, _value, source, offset) do
    # Scan forward to find end of hex literal
    scan_token_len(source, offset)
  end
  defp token_byte_length(:binary_integer, _value, source, offset) do
    scan_token_len(source, offset)
  end
  defp token_byte_length(:octal_integer, _value, source, offset) do
    scan_token_len(source, offset)
  end
  defp token_byte_length(:float, value, _source, _offset) when is_float(value),
    do: byte_size(Float.to_string(value))
  defp token_byte_length(type, value, _source, _offset) when is_binary(value) do
    # For identifiers, keywords, operators — the value IS the text
    _ = type
    byte_size(value)
  end
  defp token_byte_length(:interpolated_string, _parts, source, offset) do
    # Scan to find matching end quote
    scan_string_len(source, offset)
  end
  defp token_byte_length(_type, _value, source, offset) do
    # Fallback: scan forward to next whitespace/delimiter
    scan_token_len(source, offset)
  end

  # Scan forward from offset to find the end of a non-whitespace token.
  defp scan_token_len(source, offset) do
    rest = binary_part(source, offset, byte_size(source) - offset)
    do_scan_token_len(rest, 0)
  end

  defp do_scan_token_len(<<>>, len), do: max(len, 1)
  defp do_scan_token_len(<<c, _::binary>>, len)
       when c in [?\s, ?\t, ?\r, ?\n, ?(, ?), ?[, ?], ?{, ?}, ?,, ?;] and len > 0,
       do: len
  defp do_scan_token_len(<<_, rest::binary>>, len),
    do: do_scan_token_len(rest, len + 1)

  # Scan forward from a quote to find the end of a string.
  defp scan_string_len(source, offset) do
    rest = binary_part(source, offset, byte_size(source) - offset)
    do_scan_string_len(rest, 0, false)
  end

  defp do_scan_string_len(<<>>, len, _), do: len
  defp do_scan_string_len(<<"\\", _, rest::binary>>, len, started),
    do: do_scan_string_len(rest, len + 2, started)
  defp do_scan_string_len(<<"\"", rest::binary>>, len, true),
    do: len + 1  # found closing quote
  defp do_scan_string_len(<<"\"", rest::binary>>, len, false),
    do: do_scan_string_len(rest, len + 1, true)
  defp do_scan_string_len(<<_, rest::binary>>, len, started),
    do: do_scan_string_len(rest, len + 1, started)

  # Find the first token index whose end_offset > target.
  defp find_first_after([], _target, idx), do: idx
  defp find_first_after([ct | rest], target, idx) do
    if ct.end_offset > target do
      idx
    else
      find_first_after(rest, target, idx + 1)
    end
  end

  # Byte offset of the start of the line containing `offset`.
  defp line_start(_source, 0), do: 0

  defp line_start(source, offset) do
    case :binary.matches(binary_part(source, 0, offset), "\n") do
      [] -> 0
      matches -> elem(List.last(matches), 0) + 1
    end
  end

  # Find the index of the first token starting at or past old_end.
  defp find_last_affected(tokens, old_end, from) do
    tokens
    |> Enum.drop(from)
    |> Enum.with_index(from)
    |> Enum.find(fn {ct, _idx} -> ct.start_offset >= old_end end)
    |> case do
      {_ct, idx} -> idx
      nil -> length(tokens)
    end
  end
end
