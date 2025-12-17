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

  alias Phronesis.{Lexer, Parser, Interpreter, Compiler, State}

  # ============================================================
  # Parsing API
  # ============================================================

  @doc """
  Parse Phronesis source code into an AST.

  ## Examples

      iex> Phronesis.parse("CONST x = 42")
      {:ok, [{:const, "x", {:literal, :integer, 42}}]}

      iex> {:error, {:parse_error, msg, 1, 1, _details}} = Phronesis.parse("INVALID SYNTAX")
      iex> msg =~ "expected"
      true
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

  # ============================================================
  # Compiler API
  # ============================================================

  @doc """
  Compile source code to bytecode.

  ## Options

  - `:optimize` - Enable optimizations (default: true)

  ## Examples

      iex> {:ok, bytecode} = Phronesis.compile("CONST x = 42")
      iex> bytecode.magic
      "PHRC"
  """
  @spec compile(String.t(), keyword()) :: {:ok, Compiler.bytecode()} | {:error, term()}
  def compile(source, opts \\ []) when is_binary(source) do
    Compiler.compile(source, opts)
  end

  @doc """
  Compile an AST to bytecode.
  """
  @spec compile_ast(list(), keyword()) :: {:ok, Compiler.bytecode()} | {:error, term()}
  def compile_ast(ast, opts \\ []) when is_list(ast) do
    Compiler.compile_ast(ast, "", opts)
  end

  @doc """
  Save compiled bytecode to a .phrc file.

  ## Example

      {:ok, bytecode} = Phronesis.compile("CONST x = 42")
      :ok = Phronesis.save_compiled(bytecode, "policy.phrc")
  """
  @spec save_compiled(Compiler.bytecode(), Path.t()) :: :ok | {:error, term()}
  def save_compiled(bytecode, path) do
    Compiler.save(bytecode, path)
  end

  @doc """
  Load compiled bytecode from a .phrc file.

  ## Example

      {:ok, bytecode} = Phronesis.load_compiled("policy.phrc")
      {:ok, state} = Phronesis.execute_compiled(bytecode, state)
  """
  @spec load_compiled(Path.t()) :: {:ok, Compiler.bytecode()} | {:error, term()}
  def load_compiled(path) do
    Compiler.load(path)
  end

  @doc """
  Execute compiled bytecode.
  """
  @spec execute_compiled(Compiler.bytecode(), State.t()) :: {:ok, State.t()} | {:error, term()}
  def execute_compiled(bytecode, %State{} = state) do
    Compiler.execute(bytecode, state)
  end

  @doc """
  Disassemble bytecode to human-readable format.
  """
  @spec disassemble(Compiler.bytecode()) :: String.t()
  def disassemble(bytecode) do
    Compiler.disassemble(bytecode)
  end

  @doc """
  Compile and save a source file to .phrc.

  ## Example

      :ok = Phronesis.compile_file("policy.phr", "policy.phrc")
  """
  @spec compile_file(Path.t(), Path.t(), keyword()) :: :ok | {:error, term()}
  def compile_file(source_path, output_path, opts \\ []) do
    with {:ok, source} <- File.read(source_path),
         {:ok, bytecode} <- compile(source, opts) do
      save_compiled(bytecode, output_path)
    end
  end
end
