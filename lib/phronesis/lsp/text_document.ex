# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.LSP.TextDocument do
  @moduledoc """
  Represents an open text document in the LSP server.

  Tracks document URI, content, version, and cached parse results.
  """

  @type t :: %__MODULE__{
          uri: String.t(),
          text: String.t(),
          version: integer(),
          ast: term() | nil,
          tokens: [term()] | nil
        }

  defstruct [
    :uri,
    :text,
    :version,
    :ast,
    :tokens
  ]

  @doc """
  Create a new text document.
  """
  def new(uri, text, version \\ 0) do
    %__MODULE__{
      uri: uri,
      text: text,
      version: version,
      ast: nil,
      tokens: nil
    }
  end

  @doc """
  Get AST for document, parsing if necessary.
  """
  def get_ast(document) do
    case document.ast do
      nil ->
        case Phronesis.parse(document.text) do
          {:ok, ast} -> {:ok, %{document | ast: ast}}
          {:error, _} = err -> err
        end

      ast ->
        {:ok, %{document | ast: ast}}
    end
  end

  @doc """
  Get tokens for document, lexing if necessary.
  """
  def get_tokens(document) do
    case document.tokens do
      nil ->
        case Phronesis.Lexer.tokenize(document.text) do
          {:ok, tokens} -> {:ok, %{document | tokens: tokens}}
          {:error, _} = err -> err
        end

      tokens ->
        {:ok, %{document | tokens: tokens}}
    end
  end

  @doc """
  Get the word at a given position.
  """
  def word_at_position(document, position) do
    line_idx = position["line"]
    char_idx = position["character"]

    lines = String.split(document.text, "\n")

    case Enum.at(lines, line_idx) do
      nil ->
        nil

      line ->
        # Find word boundaries around character position
        before = String.slice(line, 0, char_idx)
        after_text = String.slice(line, char_idx, String.length(line))

        # Extract word before cursor
        word_before =
          before
          |> String.reverse()
          |> String.split(~r/[^a-zA-Z0-9_.]/, parts: 2)
          |> List.first()
          |> String.reverse()

        # Extract word after cursor
        word_after =
          after_text
          |> String.split(~r/[^a-zA-Z0-9_]/, parts: 2)
          |> List.first()

        word_before <> word_after
    end
  end

  @doc """
  Get the line at a given line index.
  """
  def get_line(document, line_idx) do
    lines = String.split(document.text, "\n")
    Enum.at(lines, line_idx)
  end
end
