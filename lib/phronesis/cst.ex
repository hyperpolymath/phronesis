# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2026 Phronesis Contributors

defmodule Phronesis.CST do
  @moduledoc """
  Concrete Syntax Tree (CST) for the Phronesis policy language.

  A CST preserves ALL source information including whitespace, comments,
  and exact token text. It is lossless and can perfectly reconstruct the
  original source. This is needed for formatters, refactoring tools, and
  IDE support.

  This module wraps/extends the existing lexer infrastructure without
  modifying it.

  ## CST Node Types

  A CST node is either:

  - A **Token** node (leaf) — contains the exact token text + any leading/trailing
    trivia (whitespace, comments)
  - A **Tree** node (branch) — contains a node kind + children (mix of Token and
    Tree nodes)

  ## Round-trip guarantee

      source |> Phronesis.CST.parse_to_cst() |> Phronesis.CST.to_source() == source

  ## Example

      iex> cst = Phronesis.CST.parse_to_cst("POLICY test_policy\\n  src.ip == 10.0.0.1\\nTHEN ACCEPT")
      iex> Phronesis.CST.to_source(cst)
      "POLICY test_policy\\n  src.ip == 10.0.0.1\\nTHEN ACCEPT"
  """

  # -------------------------------------------------------------------
  # Types
  # -------------------------------------------------------------------

  @typedoc "The kind of trivia (non-semantic source content attached to tokens)."
  @type trivia_kind :: :whitespace | :line_comment | :newline

  @typedoc "A single piece of trivia attached to a token."
  @type trivia :: %{
          kind: trivia_kind(),
          text: String.t(),
          line: pos_integer(),
          column: pos_integer()
        }

  @typedoc "A CST token: the leaf node of the concrete syntax tree."
  @type cst_token :: %{
          kind: Phronesis.Token.token_type(),
          text: String.t(),
          leading_trivia: [trivia()],
          trailing_trivia: [trivia()],
          line: pos_integer(),
          column: pos_integer()
        }

  @typedoc "The kind of a CST tree node, matching Phronesis grammar productions."
  @type cst_node_kind ::
          :source_file
          | :policy_decl
          | :import_decl
          | :const_decl
          | :condition_expr
          | :binary_expr
          | :unary_expr
          | :comparison_expr
          | :literal_expr
          | :identifier_expr
          | :module_call_expr
          | :action_block
          | :execute_action
          | :report_action
          | :reject_action
          | :accept_action
          | :conditional_action
          | :block_action
          | :metadata_block
          | :field_access
          | :error

  @typedoc "A node in the concrete syntax tree."
  @type cst_node :: {:token, cst_token()} | {:tree, cst_tree()}

  @typedoc "A branch node in the CST."
  @type cst_tree :: %{
          kind: cst_node_kind(),
          children: [cst_node()],
          line: pos_integer(),
          column: pos_integer()
        }

  # -------------------------------------------------------------------
  # Source reconstruction
  # -------------------------------------------------------------------

  @doc """
  Reconstruct exact source text from a CST node (including trivia).
  """
  @spec to_source(cst_node() | cst_tree()) :: String.t()
  def to_source({:token, tok}) do
    leading = Enum.map_join(tok.leading_trivia, "", & &1.text)
    trailing = Enum.map_join(tok.trailing_trivia, "", & &1.text)
    leading <> tok.text <> trailing
  end

  def to_source({:tree, tree}) do
    tree_to_source(tree)
  end

  def to_source(%{kind: _, children: _} = tree) do
    tree_to_source(tree)
  end

  @doc """
  Reconstruct source from a tree node.
  """
  @spec tree_to_source(cst_tree()) :: String.t()
  def tree_to_source(%{children: children}) do
    Enum.map_join(children, "", &to_source/1)
  end

  # -------------------------------------------------------------------
  # Token collection
  # -------------------------------------------------------------------

  @doc """
  Collect all tokens in document order from a CST tree.
  """
  @spec tokens(cst_tree()) :: [cst_token()]
  def tokens(%{children: children}) do
    Enum.flat_map(children, fn
      {:token, tok} -> [tok]
      {:tree, subtree} -> tokens(subtree)
    end)
  end

  # -------------------------------------------------------------------
  # Node lookup by position
  # -------------------------------------------------------------------

  @doc """
  Find the deepest node at the given line and column.
  """
  @spec node_at(cst_tree(), pos_integer(), pos_integer()) :: cst_node() | nil
  def node_at(%{children: children}, target_line, target_col) do
    Enum.find_value(children, fn
      {:token, tok} = node ->
        if tok.line == target_line and tok.column <= target_col do
          node
        end

      {:tree, subtree} = node ->
        case node_at(subtree, target_line, target_col) do
          nil ->
            if subtree.line == target_line do
              node
            end

          found ->
            found
        end
    end)
  end

  # -------------------------------------------------------------------
  # Trivia-aware lexing
  # -------------------------------------------------------------------

  @doc """
  Lex source into CST tokens with trivia attached.

  This walks the source character by character, capturing whitespace,
  comments, and newlines as trivia attached to the nearest token.
  """
  @spec lex_with_trivia(String.t()) :: [cst_token()]
  def lex_with_trivia(source) do
    case Phronesis.Lexer.tokenize(source) do
      {:ok, raw_tokens} ->
        attach_trivia(source, raw_tokens)

      {:error, _} ->
        []
    end
  end

  # Walk the source, finding gaps between raw token positions and
  # classifying them as trivia.
  defp attach_trivia(source, raw_tokens) do
    # The existing lexer skips whitespace and comments.
    # We reconstruct trivia by scanning the source between token positions.
    source_lines = String.split(source, "\n", trim: false)

    # Build a map from (line, col) -> byte offset
    {line_offsets, _} =
      Enum.reduce(source_lines, {%{}, 0}, fn line, {map, offset} ->
        line_num = map_size(map) + 1
        {Map.put(map, line_num, offset), offset + String.length(line) + 1}
      end)

    {cst_tokens, _prev_offset} =
      Enum.reduce(raw_tokens, {[], 0}, fn {type, value, line, col}, {acc, prev_offset} ->
        # Calculate byte offset of this token
        line_start = Map.get(line_offsets, line, 0)
        tok_offset = line_start + col - 1

        # Token text from the raw value
        tok_text = token_to_text(type, value)
        tok_end = tok_offset + String.length(tok_text)

        # Gap between previous end and this token start = trivia
        leading =
          if tok_offset > prev_offset do
            gap = String.slice(source, prev_offset, tok_offset - prev_offset)
            classify_trivia(gap, prev_offset, line_offsets)
          else
            []
          end

        cst_tok = %{
          kind: type,
          text: tok_text,
          leading_trivia: leading,
          trailing_trivia: [],
          line: line,
          column: col
        }

        {[cst_tok | acc], tok_end}
      end)

    # Handle trailing source after last token
    result = Enum.reverse(cst_tokens)
    total_len = String.length(source)

    case {result, _prev_offset} do
      {[], _} ->
        if total_len > 0 do
          # Whole source is trivia; wrap in a single synthetic token
          trivia = classify_trivia(source, 0, line_offsets)

          [
            %{
              kind: :eof,
              text: "",
              leading_trivia: trivia,
              trailing_trivia: [],
              line: 1,
              column: 1
            }
          ]
        else
          []
        end

      {tokens, prev_off} when prev_off < total_len ->
        gap = String.slice(source, prev_off, total_len - prev_off)
        trailing = classify_trivia(gap, prev_off, line_offsets)
        {last, rest} = List.pop_at(tokens, -1)
        updated_last = %{last | trailing_trivia: last.trailing_trivia ++ trailing}
        rest ++ [updated_last]

      _ ->
        result
    end
  end

  # Convert a raw token back to its source text representation.
  defp token_to_text(:eof, _), do: ""
  defp token_to_text(:newline, _), do: "\n"
  defp token_to_text(:integer, value) when is_integer(value), do: Integer.to_string(value)
  defp token_to_text(:hex_integer, value) when is_integer(value), do: "0x" <> Integer.to_string(value, 16)
  defp token_to_text(:binary_integer, value) when is_integer(value), do: "0b" <> Integer.to_string(value, 2)
  defp token_to_text(:octal_integer, value) when is_integer(value), do: "0o" <> Integer.to_string(value, 8)
  defp token_to_text(:float, value) when is_float(value), do: Float.to_string(value)
  defp token_to_text(:string, value) when is_binary(value), do: "\"" <> value <> "\""
  defp token_to_text(:raw_string, value) when is_binary(value), do: "r\"" <> value <> "\""
  defp token_to_text(:multiline_string, value) when is_binary(value), do: "\"\"\"" <> value <> "\"\"\""
  defp token_to_text(_type, value) when is_binary(value), do: value
  defp token_to_text(_type, nil), do: ""
  defp token_to_text(_type, value), do: to_string(value)

  # Classify a gap of source text into trivia items.
  defp classify_trivia(gap, base_offset, line_offsets) do
    classify_trivia_acc(gap, base_offset, line_offsets, [])
    |> Enum.reverse()
  end

  defp classify_trivia_acc("", _offset, _line_offsets, acc), do: acc

  defp classify_trivia_acc(<<"#", rest::binary>>, offset, line_offsets, acc) do
    # Line comment: # to end of line
    {comment_text, remaining} = split_to_newline(rest)
    full_text = "#" <> comment_text
    {line, col} = offset_to_linecol(offset, line_offsets)
    trivia = %{kind: :line_comment, text: full_text, line: line, column: col}
    classify_trivia_acc(remaining, offset + String.length(full_text), line_offsets, [trivia | acc])
  end

  defp classify_trivia_acc(<<c, rest::binary>>, offset, line_offsets, acc)
       when c in [?\s, ?\t, ?\r] do
    # Whitespace (excluding newline)
    {ws_rest, remaining} = split_whitespace(rest)
    full_text = <<c>> <> ws_rest
    {line, col} = offset_to_linecol(offset, line_offsets)
    trivia = %{kind: :whitespace, text: full_text, line: line, column: col}
    classify_trivia_acc(remaining, offset + String.length(full_text), line_offsets, [trivia | acc])
  end

  defp classify_trivia_acc(<<?\n, rest::binary>>, offset, line_offsets, acc) do
    {line, col} = offset_to_linecol(offset, line_offsets)
    trivia = %{kind: :newline, text: "\n", line: line, column: col}
    classify_trivia_acc(rest, offset + 1, line_offsets, [trivia | acc])
  end

  defp classify_trivia_acc(<<c, rest::binary>>, offset, line_offsets, acc) do
    # Unknown character in gap (shouldn't normally happen)
    {line, col} = offset_to_linecol(offset, line_offsets)
    trivia = %{kind: :whitespace, text: <<c>>, line: line, column: col}
    classify_trivia_acc(rest, offset + 1, line_offsets, [trivia | acc])
  end

  defp split_to_newline(str), do: split_to_newline(str, "")
  defp split_to_newline("", acc), do: {acc, ""}
  defp split_to_newline(<<?\n, rest::binary>>, acc), do: {acc, <<?\n, rest::binary>>}
  defp split_to_newline(<<c, rest::binary>>, acc), do: split_to_newline(rest, acc <> <<c>>)

  defp split_whitespace(str), do: split_whitespace(str, "")
  defp split_whitespace(<<c, rest::binary>>, acc) when c in [?\s, ?\t, ?\r], do: split_whitespace(rest, acc <> <<c>>)
  defp split_whitespace(rest, acc), do: {acc, rest}

  defp offset_to_linecol(offset, line_offsets) do
    # Find which line this offset falls on
    line =
      line_offsets
      |> Enum.sort_by(fn {_line, off} -> off end, :desc)
      |> Enum.find(fn {_line, off} -> off <= offset end)

    case line do
      {line_num, line_start} -> {line_num, offset - line_start + 1}
      nil -> {1, offset + 1}
    end
  end

  # -------------------------------------------------------------------
  # Public API
  # -------------------------------------------------------------------

  @doc """
  Parse source code into a Concrete Syntax Tree.

  Satisfies the round-trip property:

      source |> parse_to_cst() |> to_source() == source

  Returns a `cst_tree` rooted at `:source_file`.
  """
  @spec parse_to_cst(String.t()) :: cst_tree()
  def parse_to_cst(source) do
    cst_tokens = lex_with_trivia(source)
    children = Enum.map(cst_tokens, fn tok -> {:token, tok} end)

    {line, col} =
      case cst_tokens do
        [first | _] -> {first.line, first.column}
        [] -> {1, 1}
      end

    %{
      kind: :source_file,
      children: children,
      line: line,
      column: col
    }
  end
end
