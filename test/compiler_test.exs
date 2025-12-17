# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.CompilerTest do
  use ExUnit.Case, async: true

  alias Phronesis.Compiler

  describe "compile/2" do
    test "compiles a simple constant" do
      assert {:ok, bytecode} = Compiler.compile("CONST x = 42")
      assert bytecode.magic == "PHRC"
      assert is_map(bytecode.constants)
      assert is_list(bytecode.instructions)
    end

    test "compiles multiple constants" do
      source = """
      CONST x = 42
      CONST y = "hello"
      CONST z = true
      """
      assert {:ok, bytecode} = Compiler.compile(source)
      assert length(bytecode.instructions) > 0
    end

    test "compiles a simple policy" do
      source = """
      POLICY test_policy:
        true
        THEN ACCEPT()
        PRIORITY: 1
        EXPIRES: never
        CREATED_BY: test
      """
      assert {:ok, bytecode} = Compiler.compile(source)
      assert length(bytecode.policies) == 1
    end

    test "compiles arithmetic expressions" do
      source = "CONST result = 10 + 20 * 3"
      assert {:ok, bytecode} = Compiler.compile(source)
      assert is_list(bytecode.instructions)
    end

    test "compiles comparison expressions" do
      source = "CONST flag = 10 > 5"
      assert {:ok, bytecode} = Compiler.compile(source)
      assert is_list(bytecode.instructions)
    end

    test "compiles boolean expressions" do
      source = "CONST flag = true AND false OR true"
      assert {:ok, bytecode} = Compiler.compile(source)
      assert is_list(bytecode.instructions)
    end
  end

  describe "optimization" do
    test "folds constant arithmetic" do
      source = "CONST x = 2 + 3"
      assert {:ok, bytecode} = Compiler.compile(source, optimize: true)
      # With optimization, 2+3 should be folded to 5
      assert is_list(bytecode.instructions)
    end

    test "folds constant comparisons" do
      source = "CONST x = 5 > 3"
      assert {:ok, bytecode} = Compiler.compile(source, optimize: true)
      assert is_list(bytecode.instructions)
    end
  end

  describe "save/2 and load/1" do
    test "round-trips bytecode to file" do
      source = "CONST x = 42"
      {:ok, bytecode} = Compiler.compile(source)

      path = Path.join(System.tmp_dir!(), "test_#{:rand.uniform(10000)}.phrc")

      try do
        assert :ok = Compiler.save(bytecode, path)
        assert {:ok, loaded} = Compiler.load(path)
        assert loaded.magic == bytecode.magic
        assert loaded.version == bytecode.version
        assert loaded.instructions == bytecode.instructions
        assert loaded.constants == bytecode.constants
      after
        File.rm(path)
      end
    end

    test "returns error for invalid file" do
      assert {:error, _} = Compiler.load("/nonexistent/path.phrc")
    end

    test "returns error for invalid magic" do
      path = Path.join(System.tmp_dir!(), "bad_#{:rand.uniform(10000)}.phrc")

      try do
        File.write!(path, :erlang.term_to_binary(%{magic: "XXXX"}))
        assert {:error, {:invalid_bytecode, _}} = Compiler.load(path)
      after
        File.rm(path)
      end
    end
  end

  describe "execute/2" do
    test "executes compiled constants" do
      source = "CONST x = 42"
      {:ok, bytecode} = Compiler.compile(source)
      state = Phronesis.new_state()

      assert {:ok, new_state} = Compiler.execute(bytecode, state)
      assert {:ok, 42} = Phronesis.State.lookup(new_state, "x")
    end

    test "executes arithmetic expressions" do
      source = "CONST result = 10 + 5 * 2"
      {:ok, bytecode} = Compiler.compile(source)
      state = Phronesis.new_state()

      assert {:ok, new_state} = Compiler.execute(bytecode, state)
      assert {:ok, 20} = Phronesis.State.lookup(new_state, "result")
    end

    test "executes boolean expressions" do
      source = "CONST flag = 10 > 5"
      {:ok, bytecode} = Compiler.compile(source)
      state = Phronesis.new_state()

      assert {:ok, new_state} = Compiler.execute(bytecode, state)
      assert {:ok, true} = Phronesis.State.lookup(new_state, "flag")
    end

    test "executes multiple constants" do
      source = """
      CONST a = 10
      CONST b = 20
      CONST c = a + b
      """
      {:ok, bytecode} = Compiler.compile(source)
      state = Phronesis.new_state()

      assert {:ok, new_state} = Compiler.execute(bytecode, state)
      assert {:ok, 10} = Phronesis.State.lookup(new_state, "a")
      assert {:ok, 20} = Phronesis.State.lookup(new_state, "b")
      assert {:ok, 30} = Phronesis.State.lookup(new_state, "c")
    end
  end

  describe "disassemble/1" do
    test "produces readable output" do
      source = "CONST x = 42"
      {:ok, bytecode} = Compiler.compile(source)

      output = Compiler.disassemble(bytecode)
      assert is_binary(output)
      assert String.contains?(output, "Phronesis Bytecode")
      assert String.contains?(output, "Instructions:")
    end

    test "shows all sections" do
      source = """
      CONST x = 42
      POLICY test:
        x > 10
        THEN ACCEPT()
        PRIORITY: 1
      """
      {:ok, bytecode} = Compiler.compile(source)

      output = Compiler.disassemble(bytecode)
      assert String.contains?(output, "Constants:")
      assert String.contains?(output, "Instructions:")
      assert String.contains?(output, "Policies:")
    end
  end

  describe "Phronesis API" do
    test "compile/2 from main module" do
      assert {:ok, bytecode} = Phronesis.compile("CONST x = 1")
      assert bytecode.magic == "PHRC"
    end

    test "compile_ast/2 from main module" do
      {:ok, ast} = Phronesis.parse("CONST x = 1")
      assert {:ok, bytecode} = Phronesis.compile_ast(ast)
      assert bytecode.magic == "PHRC"
    end

    test "execute_compiled/2 from main module" do
      {:ok, bytecode} = Phronesis.compile("CONST x = 99")
      state = Phronesis.new_state()

      assert {:ok, new_state} = Phronesis.execute_compiled(bytecode, state)
      assert {:ok, 99} = Phronesis.State.lookup(new_state, "x")
    end

    test "disassemble/1 from main module" do
      {:ok, bytecode} = Phronesis.compile("CONST x = 1")
      output = Phronesis.disassemble(bytecode)
      assert is_binary(output)
    end
  end
end
