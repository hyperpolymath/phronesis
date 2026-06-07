# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.LSP.Definition do
  @moduledoc """
  Go-to-definition for Phronesis LSP.

  Finds definition locations for:
  - Constants
  - Policy names
  - Imported modules
  """

  alias Phronesis.LSP.TextDocument

  @doc """
  Find definition location(s) for a symbol at the given position.
  """
  def compute(document, position, _all_documents) do
    word = TextDocument.word_at_position(document, position)

    case word do
      nil ->
        []

      word ->
        find_definition(document, word)
    end
  end

  defp find_definition(document, symbol) do
    case TextDocument.get_ast(document) do
      {:ok, updated_doc} ->
        find_in_ast(updated_doc, symbol)

      {:error, _} ->
        []
    end
  end

  defp find_in_ast(document, symbol) do
    case find_declaration_line(document.text, symbol) do
      nil ->
        []

      line_idx ->
        [
          %{
            "uri" => document.uri,
            "range" => %{
              "start" => %{"line" => line_idx, "character" => 0},
              "end" => %{"line" => line_idx, "character" => 0}
            }
          }
        ]
    end
  end

  defp find_declaration_line(text, symbol) do
    lines = String.split(text, "\n")

    Enum.find_index(lines, fn line ->
      # Match CONST, POLICY, or IMPORT declarations
      String.match?(line, ~r/\b(CONST|POLICY)\s+#{Regex.escape(symbol)}\b/) or
        String.contains?(line, "IMPORT #{symbol}")
    end)
  end
end
