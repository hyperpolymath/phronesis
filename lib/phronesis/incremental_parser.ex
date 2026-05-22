# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

defmodule Phronesis.IncrementalParser do
  @moduledoc """
  Incremental parser for the Phronesis policy language.

  Wraps the existing `Phronesis.Parser` to provide incremental re-parsing.
  Instead of re-parsing the entire file on every edit, we cache top-level
  declarations (policies, imports, constants) with byte ranges and re-parse
  only the affected declarations when an edit occurs.

  ## Strategy

  1. Cache the full source and a list of `cached_decl` maps with byte ranges.
  2. On edit, apply the text change, find overlapping declarations.
  3. Re-parse only those declarations via `Phronesis.Parser.parse_recovering/1`.
  4. Splice the new declarations into the cache, adjusting byte offsets.

  ## Immutable Design

  All operations return a new state struct rather than mutating in place,
  following Elixir conventions.
  """

  alias Phronesis.{Lexer, Parser}

  @type edit :: %{
          start: non_neg_integer(),
          old_end: non_neg_integer(),
          new_text: String.t()
        }

  @type cached_decl :: %{
          kind: String.t(),
          start: non_neg_integer(),
          end_: non_neg_integer(),
          decl: term()
        }

  @type diagnostic :: %{
          message: String.t(),
          offset: non_neg_integer()
        }

  @type t :: %__MODULE__{
          source: String.t(),
          items: [cached_decl()],
          errors: [term()]
        }

  defstruct source: "", items: [], errors: []

  @doc """
  Create a new incremental parser by performing a full initial parse.
  """
  @spec new(String.t()) :: t()
  def new(source) when is_binary(source) do
    {items, errors} = full_parse(source)

    %__MODULE__{
      source: source,
      items: items,
      errors: errors
    }
  end

  @doc """
  Apply a text edit and re-parse only the affected declarations.

  Returns `{new_state, diagnostics}` where `diagnostics` is a list of
  diagnostic maps from the re-parsed region.
  """
  @spec edit(t(), edit()) :: {t(), [diagnostic()]}
  def edit(%__MODULE__{} = state, %{start: start, old_end: old_end, new_text: new_text}) do
    edit_len_diff = byte_size(new_text) - (old_end - start)

    # 1. Apply text edit to source
    before = binary_part(state.source, 0, start)
    after_text = binary_part(state.source, old_end, byte_size(state.source) - old_end)
    new_source = before <> new_text <> after_text

    # 2. Find affected items
    {first_affected, last_affected} = find_affected(state.items, start, old_end)

    case {first_affected, last_affected} do
      {nil, _} ->
        # No overlap — full re-parse
        {items, errors} = full_parse(new_source)

        diagnostics =
          Enum.map(errors, fn err ->
            %{message: inspect(err), offset: 0}
          end)

        {%__MODULE__{source: new_source, items: items, errors: errors}, diagnostics}

      {first, last} ->
        items_list = state.items

        # 3. Determine re-parse range
        first_item = Enum.at(items_list, first)
        last_item = Enum.at(items_list, last)
        reparse_start = first_item.start
        old_reparse_end = last_item.end_
        reparse_end = min(old_reparse_end + edit_len_diff, byte_size(new_source))
        fragment_len = max(reparse_end - reparse_start, 0)
        fragment = binary_part(new_source, reparse_start, fragment_len)

        # 4. Re-parse the fragment
        {new_cached, diagnostics, errors} = parse_fragment(fragment, reparse_start)

        # 5. Splice: replace affected items, adjust offsets for items after
        before_items = Enum.take(items_list, first)

        after_items =
          items_list
          |> Enum.drop(last + 1)
          |> Enum.map(fn item ->
            %{item | start: item.start + edit_len_diff, end_: item.end_ + edit_len_diff}
          end)

        new_items = before_items ++ new_cached ++ after_items

        new_state = %__MODULE__{
          source: new_source,
          items: new_items,
          errors: errors
        }

        {new_state, diagnostics}
    end
  end

  @doc """
  Return the list of cached declarations.
  """
  @spec items(t()) :: [cached_decl()]
  def items(%__MODULE__{items: items}), do: items

  @doc """
  Reconstruct the full AST (list of declarations) from the cached items.
  """
  @spec full_ast(t()) :: [term()]
  def full_ast(%__MODULE__{items: items}) do
    Enum.map(items, & &1.decl)
  end

  @doc """
  Return the current source text.
  """
  @spec source(t()) :: String.t()
  def source(%__MODULE__{source: source}), do: source

  # ──────────────────────────────────────────────────────────────────
  # Private helpers
  # ──────────────────────────────────────────────────────────────────

  # Perform a full parse and return {cached_items, errors}.
  defp full_parse(source) do
    case Lexer.tokenize(source) do
      {:ok, tokens} ->
        case Parser.parse_recovering(tokens) do
          {:ok, ast, diagnostics} ->
            items = build_cache(ast, source)
            {items, diagnostics}

          {:error, reason} ->
            {[], [reason]}
        end

      {:error, reason} ->
        {[], [reason]}
    end
  end

  # Parse a source fragment and return {cached_items, diagnostics, raw_errors}.
  defp parse_fragment(fragment, offset) do
    case Lexer.tokenize(fragment) do
      {:ok, tokens} ->
        case Parser.parse_recovering(tokens) do
          {:ok, ast, raw_errors} ->
            cached = build_cache(ast, fragment)

            cached =
              Enum.map(cached, fn item ->
                %{item | start: item.start + offset, end_: item.end_ + offset}
              end)

            diagnostics =
              Enum.map(raw_errors, fn err ->
                %{message: inspect(err), offset: offset}
              end)

            {cached, diagnostics, raw_errors}

          {:error, reason} ->
            {[], [%{message: inspect(reason), offset: offset}], [reason]}
        end

      {:error, reason} ->
        {[], [%{message: inspect(reason), offset: offset}], [reason]}
    end
  end

  # Build cached declarations from a parsed AST and source text.
  defp build_cache(ast, source) when is_list(ast) do
    boundaries = find_decl_boundaries(source)
    n_decls = length(ast)
    n_bounds = length(boundaries)
    source_len = byte_size(source)

    cond do
      n_decls == 0 ->
        []

      n_bounds == n_decls ->
        ast
        |> Enum.with_index()
        |> Enum.map(fn {decl, i} ->
          s = Enum.at(boundaries, i)

          e =
            if i + 1 < n_bounds do
              Enum.at(boundaries, i + 1)
            else
              source_len
            end

          %{
            kind: decl_kind(decl),
            start: s,
            end_: e,
            decl: decl
          }
        end)

      true ->
        # Fallback: distribute evenly
        ast
        |> Enum.with_index()
        |> Enum.map(fn {decl, i} ->
          s = div(i * source_len, n_decls)
          e = div((i + 1) * source_len, n_decls)

          %{
            kind: decl_kind(decl),
            start: s,
            end_: e,
            decl: decl
          }
        end)
    end
  end

  # Classify a declaration to a kind string.
  defp decl_kind({:policy, _, _, _, _}), do: "Policy"
  defp decl_kind({:import, _, _}), do: "Import"
  defp decl_kind({:const, _, _}), do: "Const"
  defp decl_kind(_), do: "Unknown"

  # Top-level keywords that can start a declaration.
  @top_keywords ["POLICY", "IMPORT", "CONST"]

  # Find byte offsets where top-level declarations begin.
  defp find_decl_boundaries(source) do
    source
    |> String.split("\n")
    |> Enum.reduce({0, []}, fn line, {offset, boundaries} ->
      trimmed = String.trim_leading(line)

      new_boundaries =
        if Enum.any?(@top_keywords, &String.starts_with?(trimmed, &1)) do
          trim_offset = offset + (byte_size(line) - byte_size(trimmed))
          [trim_offset | boundaries]
        else
          boundaries
        end

      # +1 for newline
      {offset + byte_size(line) + 1, new_boundaries}
    end)
    |> elem(1)
    |> Enum.reverse()
  end

  # Find the first and last affected items for a given edit range.
  defp find_affected(items, edit_start, edit_old_end) do
    items
    |> Enum.with_index()
    |> Enum.reduce({nil, nil}, fn {item, i}, {first, last} ->
      if item.end_ > edit_start and item.start < edit_old_end do
        first = if is_nil(first), do: i, else: first
        {first, i}
      else
        {first, last}
      end
    end)
  end
end
