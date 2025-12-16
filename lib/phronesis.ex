# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis do
  @moduledoc """
  Phronesis: A Policy Language for Network Configuration.

  A minimal, decidable DSL for expressing network policies with:
  - Consensus-gated execution
  - Formal verification guarantees
  - Modular standard library

  ## Grammar Overview

  The core grammar is ~40 lines of EBNF with 15 keywords:

      POLICY <name>:
        <condition>
        THEN <action>
        PRIORITY: <int>
        EXPIRES: <datetime> | never
        CREATED_BY: <identifier>

  ## Quick Start

      # Parse and execute a policy
      {:ok, ast} = Phronesis.parse(\"""
        POLICY block_invalid_routes:
          Std.RPKI.validate(route) == "invalid"
          THEN REJECT("Invalid RPKI")
          PRIORITY: 100
          EXPIRES: never
          CREATED_BY: security
      \""")

      {:ok, result} = Phronesis.execute(ast, environment)

  ## Design Principles

  - **Simple Syntax, Powerful Modules**: Core language is minimal;
    power comes from the Std.* module library
  - **Decidable**: No loops, guaranteed termination
  - **Consensus-Safe**: Actions require distributed agreement
  - **Auditable**: All executions logged immutably
  """

  alias Phronesis.{Lexer, Parser, Interpreter, State}

  @doc """
  Parse Phronesis source code into an AST.

  ## Examples

      iex> Phronesis.parse("CONST x = 42")
      {:ok, [{:const, "x", {:literal, :integer, 42}}]}

      iex> Phronesis.parse("INVALID SYNTAX")
      {:error, {:parse_error, "expected POLICY, IMPORT, or CONST", 1, 1}}
  """
  @spec parse(String.t()) :: {:ok, list()} | {:error, term()}
  def parse(source) when is_binary(source) do
    with {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      {:ok, ast}
    end
  end

  @doc """
  Tokenize source code into a list of tokens.

  Useful for debugging the lexer.
  """
  @spec tokenize(String.t()) :: {:ok, list()} | {:error, term()}
  def tokenize(source) when is_binary(source) do
    Lexer.tokenize(source)
  end

  @doc """
  Execute an AST with the given environment and state.

  Returns `{:ok, new_state}` on success, `{:error, reason}` on failure.

  ## Consensus Requirement

  Actions only execute if consensus is achieved (per operational semantics Rule 2).
  """
  @spec execute(list(), State.t()) :: {:ok, State.t()} | {:error, term()}
  def execute(ast, %State{} = state) do
    Interpreter.execute(ast, state)
  end

  @doc """
  Create a new execution state.

  ## Options

  - `:consensus_threshold` - Required vote percentage (default: 0.51)
  - `:agents` - List of agent IDs for consensus voting
  """
  @spec new_state(keyword()) :: State.t()
  def new_state(opts \\ []) do
    State.new(opts)
  end

  @doc """
  Load and parse a policy file.
  """
  @spec load_file(Path.t()) :: {:ok, list()} | {:error, term()}
  def load_file(path) do
    case File.read(path) do
      {:ok, source} -> parse(source)
      {:error, reason} -> {:error, {:file_error, reason}}
    end
  end
end
