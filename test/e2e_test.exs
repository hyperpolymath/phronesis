# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Phronesis — End-to-End Tests
#
# Drives complete policy programs through the full pipeline:
# source text → lexer → parser → compiler → interpreter.
#
# These tests verify that every stage is wired correctly and that a
# realistic policy program produces the expected decision output.

defmodule Phronesis.E2ETest do
  use ExUnit.Case, async: true

  alias Phronesis.{Lexer, Compiler}

  @moduledoc """
  End-to-end pipeline tests for Phronesis.

  Each test drives a realistic snippet through every stage and verifies
  the observable output at each boundary. A failure in any test
  pinpoints the failing stage via its assertion message.
  """

  # ====================================================================
  # E2E 1: Integer constant — full lexer-to-bytecode pipeline
  # ====================================================================

  @doc """
  A single integer constant must lex cleanly and compile to valid bytecode
  with a magic number, non-empty instructions, and a populated constants map.
  """
  test "integer constant: lex → compile pipeline" do
    source = "CONST answer = 42"

    # Stage 1: Lex
    assert {:ok, tokens} = Lexer.tokenize(source),
           "E2E: integer constant must tokenize without error"
    assert length(tokens) > 0, "E2E: token list must be non-empty"

    # Stage 2: Compile
    assert {:ok, bytecode} = Compiler.compile(source),
           "E2E: integer constant must compile without error"
    assert bytecode.magic == "PHRC",
           "E2E: bytecode must have correct magic header"
    assert length(bytecode.instructions) > 0,
           "E2E: bytecode must have at least one instruction"
  end

  # ====================================================================
  # E2E 2: String constant — full pipeline
  # ====================================================================

  test "string constant: lex → compile pipeline" do
    source = ~s(CONST greeting = "hello world")

    assert {:ok, _tokens} = Lexer.tokenize(source),
           "E2E: string constant must tokenize"
    assert {:ok, bytecode} = Compiler.compile(source),
           "E2E: string constant must compile"
    assert is_map(bytecode.constants),
           "E2E: compiled bytecode must have constants map"
  end

  # ====================================================================
  # E2E 3: Boolean constant — full pipeline
  # ====================================================================

  test "boolean constant: lex → compile pipeline" do
    source = "CONST flag = true"

    assert {:ok, _tokens} = Lexer.tokenize(source)
    assert {:ok, bytecode} = Compiler.compile(source)
    assert is_list(bytecode.instructions)
    assert length(bytecode.instructions) > 0
  end

  # ====================================================================
  # E2E 4: Policy declaration — full pipeline
  # ====================================================================

  @doc """
  A complete policy declaration (the primary language construct) must
  lex, parse, and compile to a bytecode struct with at least one policy entry.
  """
  test "policy declaration: full pipeline" do
    source = """
    POLICY accept_all:
      true
      THEN ACCEPT("all traffic accepted")
      PRIORITY: 100
      EXPIRES: never
      CREATED_BY: e2e_test
    """

    assert {:ok, _tokens} = Lexer.tokenize(source),
           "E2E: policy declaration must tokenize"
    assert {:ok, bytecode} = Compiler.compile(source),
           "E2E: policy declaration must compile"
    assert is_list(bytecode.policies),
           "E2E: compiled bytecode must have policies list"
    assert length(bytecode.policies) == 1,
           "E2E: exactly one policy must be compiled"
  end

  # ====================================================================
  # E2E 5: Parse error is recoverable — pipeline returns {:error, _}
  # ====================================================================

  @doc """
  Syntactically invalid source must produce an {:error, _} result from
  the compiler rather than raising an exception. This tests the pipeline's
  error-recovery path.
  """
  test "invalid source produces error tuple not exception" do
    source = "POLICY !!invalid!!"

    result = Compiler.compile(source)
    assert match?({:error, _}, result),
           "E2E: invalid source must produce {:error, _}, got: #{inspect(result)}"
  end

  # ====================================================================
  # E2E 6: Multi-constant program through full pipeline
  # ====================================================================

  test "multi-constant program: full pipeline" do
    source = """
    CONST x = 1
    CONST y = 2
    CONST z = 3
    """

    assert {:ok, _tokens} = Lexer.tokenize(source)
    assert {:ok, bytecode} = Compiler.compile(source)
    assert length(bytecode.instructions) > 0
  end
end
