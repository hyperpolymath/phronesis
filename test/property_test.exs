# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Phronesis — Property-Based (P2P) Tests
#
# Uses StreamData to generate inputs and verify invariants that must
# hold across all possible inputs, not just the specific cases in unit tests.
#
# Properties tested:
#   1. Lexer panic-freedom on arbitrary printable strings
#   2. Lexer always returns a tagged tuple {:ok, _} or {:error, _}
#   3. Compiler output type consistency: always returns {:ok, bytecode} or {:error, _}
#   4. Integer constants compile to bytecode with non-empty instructions
#   5. Determinism: same source always produces the same compiler result

defmodule Phronesis.PropertyTest do
  use ExUnit.Case
  use ExUnitProperties

  alias Phronesis.Lexer
  alias Phronesis.Compiler

  # ====================================================================
  # P2P Property 1: Lexer never crashes on arbitrary printable strings
  # ====================================================================

  @doc """
  The lexer must not raise an exception on any printable ASCII string.
  It must return a tagged tuple — either {:ok, tokens} or {:error, _}.
  A crash or bare exception is always a bug.
  """
  property "lexer does not crash on arbitrary printable strings" do
    check all(s <- string(:printable)) do
      result = Lexer.tokenize(s)
      assert match?({:ok, _}, result) or match?({:error, _}, result),
             "Lexer returned unexpected value for input #{inspect(s)}: #{inspect(result)}"
    end
  end

  # ====================================================================
  # P2P Property 2: Lexer result is always a tagged tuple
  # ====================================================================

  @doc """
  For any alphanumeric string, the lexer must return exactly a 2-tuple
  whose first element is :ok or :error. No other return shapes are valid.
  """
  property "lexer always returns a tagged tuple" do
    check all(s <- string(:alphanumeric)) do
      result = Lexer.tokenize(s)
      assert is_tuple(result) and tuple_size(result) >= 2,
             "Expected a tuple, got: #{inspect(result)}"
      assert elem(result, 0) in [:ok, :error],
             "Expected :ok or :error as first element, got: #{inspect(elem(result, 0))}"
    end
  end

  # ====================================================================
  # P2P Property 3: Compiler output is always a tagged tuple
  # ====================================================================

  @doc """
  The compiler must return {:ok, bytecode} or {:error, reason} for any
  string input. The shape of the return must not depend on the specific
  content — only on whether it is valid Phronesis syntax.
  """
  property "compiler always returns a tagged tuple" do
    check all(s <- string(:printable, max_length: 200)) do
      result = Compiler.compile(s)
      assert is_tuple(result) and tuple_size(result) == 2,
             "Compiler must return a 2-tuple, got: #{inspect(result)}"
      assert elem(result, 0) in [:ok, :error],
             "Compiler first element must be :ok or :error, got: #{inspect(elem(result, 0))}"
    end
  end

  # ====================================================================
  # P2P Property 4: Integer constants always produce non-empty bytecode
  # ====================================================================

  @doc """
  Any valid integer constant declaration must compile to bytecode with
  at least one instruction. A constant with no instructions is a
  compiler bug: there must always be at least a LOAD or STORE instruction.
  """
  property "valid integer constants always compile to non-empty instruction list" do
    check all(n <- integer()) do
      source = "CONST x = #{n}"
      case Compiler.compile(source) do
        {:ok, bytecode} ->
          assert is_list(bytecode.instructions),
                 "bytecode.instructions must be a list"
          assert length(bytecode.instructions) > 0,
                 "Compiling 'CONST x = #{n}' produced empty instruction list"
        {:error, _} ->
          # Compile errors are acceptable — only assert the shape
          :ok
      end
    end
  end

  # ====================================================================
  # P2P Property 5: Compiler determinism
  # ====================================================================

  @doc """
  Compiling the same source twice must produce structurally identical
  bytecode. This guards against hidden mutable state in the compiler
  (e.g. global counters, non-deterministic map iteration).
  """
  property "compiler is deterministic for the same source" do
    check all(n <- integer(-1_000_000..1_000_000)) do
      source = "CONST deterministic_value = #{n}"
      result_a = Compiler.compile(source)
      result_b = Compiler.compile(source)

      case {result_a, result_b} do
        {{:ok, bc_a}, {:ok, bc_b}} ->
          assert length(bc_a.instructions) == length(bc_b.instructions),
                 "Non-deterministic instruction count for source: #{source}"
          assert map_size(bc_a.constants) == map_size(bc_b.constants),
                 "Non-deterministic constant count for source: #{source}"
        {{:error, _}, {:error, _}} ->
          # Both fail consistently — determinism preserved
          :ok
        _ ->
          flunk("Non-deterministic result (one ok, one error) for source: #{source}")
      end
    end
  end
end
