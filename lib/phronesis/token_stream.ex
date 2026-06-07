# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

defmodule Phronesis.TokenStream do
  @moduledoc """
  Token Stream API for macro systems.

  This module provides the foundational token stream abstraction used by
  procedural and declarative macro systems. Macros receive a token stream
  as input, manipulate it, and produce a token stream as output.

  The design follows Rust's `proc_macro::TokenStream` as a reference but
  is adapted for Elixir/BEAM-based nextgen languages (Phronesis).

  ## Architecture

  A token stream is a list of token tree tuples. Each token tree is one of
  four tagged tuples:

  - `{:ident, name, span}` — an identifier or keyword
  - `{:punct, char, spacing, span}` — a single punctuation character
  - `{:literal, kind, text, span}` — a numeric, string, char, or boolean literal
  - `{:group, delimiter, stream, span}` — a delimited group of tokens

  Keywords are treated as identifiers at this level. Multi-character operators
  (e.g., `!=`, `->`) are represented as multiple `:punct` tuples with `:joint`
  spacing on all but the last.

  ## Example

      iex> {:ok, stream} = Phronesis.TokenStream.of_string("x + 1")
      iex> length(stream)
      3
      iex> Phronesis.TokenStream.to_source(stream)
      "x + 1"
  """

  # -------------------------------------------------------------------------
  # Types
  # -------------------------------------------------------------------------

  @typedoc """
  Source location span: `{start_offset, end_offset, file}`.
  """
  @type span :: {non_neg_integer(), non_neg_integer(), String.t()}

  @typedoc """
  Spacing for punctuation tokens.

  - `:alone` — followed by whitespace or a non-punctuation token
  - `:joint` — immediately followed by another punctuation character
  """
  @type spacing :: :alone | :joint

  @typedoc """
  The kind of a literal value.

  - `:integer` — e.g., `42`, `0xFF`
  - `:float` — e.g., `3.14`, `1.5e10`
  - `:string` — e.g., `"hello"`
  - `:char` — e.g., `'a'`
  - `:bool` — `true` or `false`
  """
  @type literal_kind :: :integer | :float | :string | :char | :bool

  @typedoc """
  Delimiter kind for groups.

  - `:paren` — `( ... )`
  - `:bracket` — `[ ... ]`
  - `:brace` — `{ ... }`
  - `:none` — invisible grouping (macro expansion)
  """
  @type delimiter :: :paren | :bracket | :brace | :none

  @typedoc """
  A single token tree — the fundamental unit of the token stream.
  """
  @type token_tree ::
          {:ident, String.t(), span()}
          | {:punct, char(), spacing(), span()}
          | {:literal, literal_kind(), String.t(), span()}
          | {:group, delimiter(), t(), span()}

  @typedoc """
  A token stream: a list of token trees.
  """
  @type t :: [token_tree()]

  @typedoc """
  Parse error: `{:error, message, offset}`.
  """
  @type parse_error :: {:error, String.t(), non_neg_integer()}

  # -------------------------------------------------------------------------
  # Constructors
  # -------------------------------------------------------------------------

  @doc """
  Creates an empty token stream.
  """
  @spec new() :: t()
  def new, do: []

  @doc """
  Creates an identifier token tree.
  """
  @spec ident(String.t(), span()) :: token_tree()
  def ident(name, span), do: {:ident, name, span}

  @doc """
  Creates a punctuation token tree.
  """
  @spec punct(char(), spacing(), span()) :: token_tree()
  def punct(ch, spacing, span), do: {:punct, ch, spacing, span}

  @doc """
  Creates a literal token tree.
  """
  @spec literal(literal_kind(), String.t(), span()) :: token_tree()
  def literal(kind, text, span), do: {:literal, kind, text, span}

  @doc """
  Creates a delimited group token tree.
  """
  @spec group(delimiter(), t(), span()) :: token_tree()
  def group(delimiter, stream, span), do: {:group, delimiter, stream, span}

  # -------------------------------------------------------------------------
  # Accessors
  # -------------------------------------------------------------------------

  @doc """
  Returns the span of a token tree.
  """
  @spec span_of(token_tree()) :: span()
  def span_of({:ident, _, span}), do: span
  def span_of({:punct, _, _, span}), do: span
  def span_of({:literal, _, _, span}), do: span
  def span_of({:group, _, _, span}), do: span

  @doc """
  Returns the span covering the entire stream, or a dummy span if empty.
  """
  @spec stream_span(t()) :: span()
  def stream_span([]), do: {0, 0, "<empty>"}

  def stream_span(trees) do
    {first_start, _, first_file} = span_of(List.first(trees))
    {_, last_end, _} = span_of(List.last(trees))
    {first_start, last_end, first_file}
  end

  @doc """
  Returns `true` if the stream is empty.
  """
  @spec empty?(t()) :: boolean()
  def empty?(stream), do: stream == []

  # -------------------------------------------------------------------------
  # Parsing — lex source text into a token stream
  # -------------------------------------------------------------------------

  @doc """
  Lexes source text into a token stream.

  Handles identifiers, keywords (as identifiers), numeric literals
  (decimal, hex, binary, octal, float), string and character literals,
  boolean literals, punctuation with correct spacing, delimiter grouping,
  and line/block comments.

  ## Options

  - `:file` — filename for span information (default: `"<input>"`)

  ## Examples

      iex> Phronesis.TokenStream.of_string("let x = 42")
      {:ok, [
        {:ident, "let", {0, 3, "<input>"}},
        {:ident, "x", {4, 5, "<input>"}},
        {:punct, ?=, :alone, {6, 7, "<input>"}},
        {:literal, :integer, "42", {8, 10, "<input>"}}
      ]}

      iex> Phronesis.TokenStream.of_string("(a)")
      {:ok, [{:group, :paren, [{:ident, "a", {1, 2, "<input>"}}], {0, 3, "<input>"}}]}
  """
  @spec of_string(String.t(), keyword()) :: {:ok, t()} | parse_error()
  def of_string(source, opts \\ []) do
    file = Keyword.get(opts, :file, "<input>")
    bytes = :binary.bin_to_list(source)

    case lex_tokens(bytes, 0, file, [], []) do
      {:ok, trees} -> {:ok, trees}
      {:error, _, _} = err -> err
    end
  end

  # -------------------------------------------------------------------------
  # Pretty-printing — reconstruct source from token stream
  # -------------------------------------------------------------------------

  @doc """
  Reconstructs source text from a token stream.

  Inserts a single space between tokens, respecting `:joint` spacing
  for multi-character operators. The output, when re-lexed, yields a
  structurally equivalent token stream.
  """
  @spec to_source(t()) :: String.t()
  def to_source(stream) do
    stream
    |> Enum.reduce({"", true}, fn tree, {acc, first?} ->
      prefix =
        if first? do
          ""
        else
          case tree do
            {:punct, _, :joint, _} -> ""
            _ -> " "
          end
        end

      {acc <> prefix <> tree_to_string(tree), false}
    end)
    |> elem(0)
  end

  @doc """
  Converts a single token tree to its string representation.
  """
  @spec tree_to_string(token_tree()) :: String.t()
  def tree_to_string({:ident, name, _span}), do: name
  def tree_to_string({:punct, ch, _spacing, _span}), do: <<ch::utf8>>
  def tree_to_string({:literal, _kind, text, _span}), do: text

  def tree_to_string({:group, delimiter, stream, _span}) do
    inner = to_source(stream)

    case delimiter do
      :paren -> "(" <> inner <> ")"
      :bracket -> "[" <> inner <> "]"
      :brace -> "{" <> inner <> "}"
      :none -> inner
    end
  end

  # -------------------------------------------------------------------------
  # Stream operations
  # -------------------------------------------------------------------------

  @doc """
  Concatenates two token streams.
  """
  @spec concat(t(), t()) :: t()
  def concat(a, b), do: a ++ b

  @doc """
  Flattens a list of token streams into one.
  """
  @spec flatten([t()]) :: t()
  def flatten(streams), do: List.flatten(streams)

  @doc """
  Appends a token tree to the end of a stream.
  """
  @spec push(t(), token_tree()) :: t()
  def push(stream, tree), do: stream ++ [tree]

  # -------------------------------------------------------------------------
  # Internal lexer
  # -------------------------------------------------------------------------

  # Punctuation characters recognised by the token stream lexer.
  # Delimiters are excluded (handled separately as group boundaries).
  @punct_chars ~c[+-*/%=!<>&|^~.,;:@#?\\]

  defp is_punct?(ch), do: ch in @punct_chars
  defp is_alpha?(ch), do: (ch >= ?a and ch <= ?z) or (ch >= ?A and ch <= ?Z) or ch == ?_
  defp is_digit?(ch), do: ch >= ?0 and ch <= ?9
  defp is_alnum?(ch), do: is_alpha?(ch) or is_digit?(ch)
  defp is_ws?(ch), do: ch in ~c[ \t\r\n]

  # Main lexer loop.
  # bytes: remaining input (charlist)
  # pos: current byte offset
  # file: filename for spans
  # stack: [(delimiter, start_pos, parent_trees)] for nesting
  # trees: accumulated token trees for current level (in reverse)
  defp lex_tokens([], pos, _file, [], trees), do: {:ok, Enum.reverse(trees)}

  defp lex_tokens([], _pos, _file, [{delim, start, _parent} | _], _trees) do
    ch = case delim do
      :paren -> "("
      :bracket -> "["
      :brace -> "{"
    end
    {:error, "unclosed delimiter '#{ch}'", start}
  end

  # Whitespace
  defp lex_tokens([ch | rest], pos, file, stack, trees) when ch in ~c[ \t\r\n] do
    lex_tokens(rest, pos + 1, file, stack, trees)
  end

  # Line comment
  defp lex_tokens([?/, ?/ | rest], pos, file, stack, trees) do
    {rest2, new_pos} = skip_line_comment(rest, pos + 2)
    lex_tokens(rest2, new_pos, file, stack, trees)
  end

  # Block comment
  defp lex_tokens([?/, ?* | rest], pos, file, stack, trees) do
    case skip_block_comment(rest, pos + 2, 1) do
      {:ok, rest2, new_pos} -> lex_tokens(rest2, new_pos, file, stack, trees)
      :error -> {:error, "unterminated block comment", pos}
    end
  end

  # Opening delimiters
  defp lex_tokens([?( | rest], pos, file, stack, trees) do
    lex_tokens(rest, pos + 1, file, [{:paren, pos, trees} | stack], [])
  end
  defp lex_tokens([?[ | rest], pos, file, stack, trees) do
    lex_tokens(rest, pos + 1, file, [{:bracket, pos, trees} | stack], [])
  end
  defp lex_tokens([?{ | rest], pos, file, stack, trees) do
    lex_tokens(rest, pos + 1, file, [{:brace, pos, trees} | stack], [])
  end

  # Closing delimiters
  defp lex_tokens([?) | rest], pos, file, [{:paren, start, parent} | stack], trees) do
    grp = {:group, :paren, Enum.reverse(trees), {start, pos + 1, file}}
    lex_tokens(rest, pos + 1, file, stack, [grp | parent])
  end
  defp lex_tokens([?] | rest], pos, file, [{:bracket, start, parent} | stack], trees) do
    grp = {:group, :bracket, Enum.reverse(trees), {start, pos + 1, file}}
    lex_tokens(rest, pos + 1, file, stack, [grp | parent])
  end
  defp lex_tokens([?} | rest], pos, file, [{:brace, start, parent} | stack], trees) do
    grp = {:group, :brace, Enum.reverse(trees), {start, pos + 1, file}}
    lex_tokens(rest, pos + 1, file, stack, [grp | parent])
  end

  # Mismatched closing delimiter
  defp lex_tokens([ch | _rest], pos, _file, [{delim, _start, _parent} | _stack], _trees)
       when ch in ~c[)\]}] do
    expected = case delim do
      :paren -> ")"
      :bracket -> "]"
      :brace -> "}"
    end
    {:error, "mismatched delimiter: expected '#{expected}', found '#{<<ch::utf8>>}'", pos}
  end

  # Unexpected closing delimiter (empty stack)
  defp lex_tokens([ch | _rest], pos, _file, [], _trees) when ch in ~c[)\]}] do
    {:error, "unexpected closing delimiter '#{<<ch::utf8>>}'", pos}
  end

  # String literal
  defp lex_tokens([?" | rest], pos, file, stack, trees) do
    case lex_string(rest, pos + 1, [?"]) do
      {:ok, text, rest2, new_pos} ->
        span = {pos, new_pos, file}
        tree = {:literal, :string, text, span}
        lex_tokens(rest2, new_pos, file, stack, [tree | trees])
      :error ->
        {:error, "unterminated string literal", pos}
    end
  end

  # Character literal
  defp lex_tokens([?' | rest], pos, file, stack, trees) do
    case lex_char_lit(rest, pos + 1) do
      {:ok, text, rest2, new_pos} ->
        span = {pos, new_pos, file}
        tree = {:literal, :char, text, span}
        lex_tokens(rest2, new_pos, file, stack, [tree | trees])
      :error ->
        {:error, "unterminated character literal", pos}
    end
  end

  # Numeric literal
  defp lex_tokens([ch | _rest] = bytes, pos, file, stack, trees) when ch >= ?0 and ch <= ?9 do
    {kind, text, rest2, new_pos} = lex_number(bytes, pos)
    span = {pos, new_pos, file}
    tree = {:literal, kind, text, span}
    lex_tokens(rest2, new_pos, file, stack, [tree | trees])
  end

  # Identifier or keyword
  defp lex_tokens([ch | _rest] = bytes, pos, file, stack, trees)
       when (ch >= ?a and ch <= ?z) or (ch >= ?A and ch <= ?Z) or ch == ?_ do
    {text, rest2, new_pos} = lex_word(bytes, pos, [])
    span = {pos, new_pos, file}
    tree = if text in ["true", "false"] do
      {:literal, :bool, text, span}
    else
      {:ident, text, span}
    end
    lex_tokens(rest2, new_pos, file, stack, [tree | trees])
  end

  # Punctuation
  defp lex_tokens([ch | rest], pos, file, stack, trees) when ch in @punct_chars do
    spacing = case rest do
      [next | _] when next in @punct_chars -> :joint
      _ -> :alone
    end
    span = {pos, pos + 1, file}
    tree = {:punct, ch, spacing, span}
    lex_tokens(rest, pos + 1, file, stack, [tree | trees])
  end

  # Unknown character
  defp lex_tokens([ch | _rest], pos, _file, _stack, _trees) do
    {:error, "unexpected character: '#{<<ch::utf8>>}'", pos}
  end

  # --- Helper lexers ---

  defp skip_line_comment([?\n | rest], pos), do: {rest, pos + 1}
  defp skip_line_comment([_ | rest], pos), do: skip_line_comment(rest, pos + 1)
  defp skip_line_comment([], pos), do: {[], pos}

  defp skip_block_comment(_, _pos, 0), do: {:ok, [], 0} # unreachable guard
  defp skip_block_comment([?*, ?/ | rest], pos, 1), do: {:ok, rest, pos + 2}
  defp skip_block_comment([?*, ?/ | rest], pos, depth), do: skip_block_comment(rest, pos + 2, depth - 1)
  defp skip_block_comment([?/, ?* | rest], pos, depth), do: skip_block_comment(rest, pos + 2, depth + 1)
  defp skip_block_comment([_ | rest], pos, depth), do: skip_block_comment(rest, pos + 1, depth)
  defp skip_block_comment([], _pos, _depth), do: :error

  defp lex_string([?\\ , ch | rest], pos, acc), do: lex_string(rest, pos + 2, [ch, ?\\ | acc])
  defp lex_string([?" | rest], pos, acc) do
    text = [?" | acc] |> Enum.reverse() |> List.to_string()
    {:ok, text, rest, pos + 1}
  end
  defp lex_string([ch | rest], pos, acc), do: lex_string(rest, pos + 1, [ch | acc])
  defp lex_string([], _pos, _acc), do: :error

  defp lex_char_lit([?\\ , ch, ?' | rest], pos) do
    text = List.to_string([?', ?\\, ch, ?'])
    {:ok, text, rest, pos + 3}
  end
  defp lex_char_lit([ch, ?' | rest], pos) do
    text = List.to_string([?', ch, ?'])
    {:ok, text, rest, pos + 2}
  end
  defp lex_char_lit(_, _pos), do: :error

  defp lex_number([?0, prefix | rest], pos) when prefix in ~c[xXbBoO] do
    {digits, rest2, new_pos} = consume_alnum(rest, pos + 2, [prefix, ?0])
    text = digits |> Enum.reverse() |> List.to_string()
    {:integer, text, rest2, new_pos}
  end
  defp lex_number(bytes, pos) do
    {int_acc, rest, new_pos} = consume_digits(bytes, pos, [])
    {kind, final_acc, rest2, final_pos} = maybe_float(rest, new_pos, int_acc)
    text = final_acc |> Enum.reverse() |> List.to_string()
    {kind, text, rest2, final_pos}
  end

  defp consume_digits([ch | rest], pos, acc) when (ch >= ?0 and ch <= ?9) or ch == ?_ do
    consume_digits(rest, pos + 1, [ch | acc])
  end
  defp consume_digits(rest, pos, acc), do: {acc, rest, pos}

  defp consume_alnum([ch | rest], pos, acc) when (ch >= ?0 and ch <= ?9) or
    (ch >= ?a and ch <= ?f) or (ch >= ?A and ch <= ?F) or ch == ?_ do
    consume_alnum(rest, pos + 1, [ch | acc])
  end
  defp consume_alnum(rest, pos, acc), do: {acc, rest, pos}

  defp maybe_float([?., next | rest], pos, acc) when next >= ?0 and next <= ?9 do
    {frac_acc, rest2, pos2} = consume_digits(rest, pos + 2, [next, ?. | acc])
    maybe_exponent(rest2, pos2, frac_acc, :float)
  end
  defp maybe_float(rest, pos, acc), do: maybe_exponent(rest, pos, acc, :integer)

  defp maybe_exponent([e | rest], pos, acc, _kind) when e in ~c[eE] do
    case rest do
      [sign | rest2] when sign in ~c[+-] ->
        {exp_acc, rest3, pos3} = consume_digits(rest2, pos + 2, [sign, e | acc])
        {:float, exp_acc, rest3, pos3}
      _ ->
        {exp_acc, rest2, pos2} = consume_digits(rest, pos + 1, [e | acc])
        {:float, exp_acc, rest2, pos2}
    end
  end
  defp maybe_exponent(rest, pos, acc, kind), do: {kind, acc, rest, pos}

  defp lex_word([ch | rest], pos, acc) when (ch >= ?a and ch <= ?z) or
    (ch >= ?A and ch <= ?Z) or (ch >= ?0 and ch <= ?9) or ch == ?_ do
    lex_word(rest, pos + 1, [ch | acc])
  end
  defp lex_word(rest, pos, acc) do
    text = acc |> Enum.reverse() |> List.to_string()
    {text, rest, pos}
  end
end
