# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Token do
  @moduledoc """
  Token definitions for the Phronesis lexer.

  ## Token Types

  The Phronesis language has 15 keywords organized into categories:

  - **Core**: POLICY, THEN, PRIORITY, EXPIRES, CREATED_BY, CONST
  - **Logic**: AND, OR, NOT
  - **Actions**: EXECUTE, REPORT, REJECT, ACCEPT
  - **Control**: IF, ELSE, BEGIN, END
  - **Modules**: IMPORT, AS
  """

  @type token_type ::
          # Core keywords
          :policy
          | :then
          | :priority
          | :expires
          | :created_by
          | :const
          # Logic keywords
          | :and
          | :or
          | :not
          # Action keywords
          | :execute
          | :report
          | :reject
          | :accept
          # Control flow
          | :if
          | :else
          | :begin
          | :end_block
          # Module keywords
          | :import
          | :as
          # Special values
          | :never
          | :true
          | :false
          | :in
          # Literals
          | :integer
          | :float
          | :string
          | :ip_address
          | :datetime
          # Identifier
          | :identifier
          # Operators
          | :plus
          | :minus
          | :star
          | :slash
          | :eq
          | :neq
          | :gt
          | :gte
          | :lt
          | :lte
          | :assign
          # Delimiters
          | :lparen
          | :rparen
          | :comma
          | :colon
          | :dot
          # Special
          | :eof
          | :newline

  @type t :: {token_type(), any(), pos_integer(), pos_integer()}

  @keywords %{
    "POLICY" => :policy,
    "THEN" => :then,
    "PRIORITY" => :priority,
    "EXPIRES" => :expires,
    "CREATED_BY" => :created_by,
    "CONST" => :const,
    "AND" => :and,
    "OR" => :or,
    "NOT" => :not,
    "EXECUTE" => :execute,
    "REPORT" => :report,
    "REJECT" => :reject,
    "ACCEPT" => :accept,
    "IF" => :if,
    "ELSE" => :else,
    "BEGIN" => :begin,
    "END" => :end_block,
    "IMPORT" => :import,
    "AS" => :as,
    "never" => :never,
    "true" => :true,
    "false" => :false,
    "IN" => :in
  }

  @doc """
  Get all keyword mappings.
  """
  @spec keywords() :: map()
  def keywords, do: @keywords

  @doc """
  Check if a string is a keyword.
  """
  @spec keyword?(String.t()) :: boolean()
  def keyword?(word) when is_binary(word) do
    Map.has_key?(@keywords, word)
  end

  @doc """
  Get the token type for a keyword, or :identifier if not a keyword.
  """
  @spec lookup_keyword(String.t()) :: token_type()
  def lookup_keyword(word) when is_binary(word) do
    Map.get(@keywords, word, :identifier)
  end

  @doc """
  Create a token tuple.
  """
  @spec new(token_type(), any(), pos_integer(), pos_integer()) :: t()
  def new(type, value, line, column) do
    {type, value, line, column}
  end

  @doc """
  Get the type from a token.
  """
  @spec type(t()) :: token_type()
  def type({type, _, _, _}), do: type

  @doc """
  Get the value from a token.
  """
  @spec value(t()) :: any()
  def value({_, value, _, _}), do: value

  @doc """
  Get the line number from a token.
  """
  @spec line(t()) :: pos_integer()
  def line({_, _, line, _}), do: line

  @doc """
  Get the column number from a token.
  """
  @spec column(t()) :: pos_integer()
  def column({_, _, _, column}), do: column
end
