# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.TypeCheckerTest do
  use ExUnit.Case, async: true

  alias Phronesis.AST
  alias Phronesis.TypeChecker

  # ------------------------------------------------------------------
  # Expression Type Inference
  # ------------------------------------------------------------------

  describe "infer_expr_type/2" do
    test "integer literal" do
      assert TypeChecker.infer_expr_type({:literal, :integer, 42}) == :integer
    end

    test "float literal" do
      assert TypeChecker.infer_expr_type({:literal, :float, 3.14}) == :float
    end

    test "string literal" do
      assert TypeChecker.infer_expr_type({:literal, :string, "hello"}) == :string
    end

    test "boolean literal" do
      assert TypeChecker.infer_expr_type({:literal, :boolean, true}) == :boolean
    end

    test "ip_address literal" do
      assert TypeChecker.infer_expr_type({:literal, :ip_address, "10.0.0.1"}) == :ip_address
    end

    test "datetime literal" do
      assert TypeChecker.infer_expr_type({:literal, :datetime, "2026-01-01T00:00:00Z"}) ==
               :datetime
    end

    test "identifier in scope" do
      scope = %{"threshold" => :float}
      assert TypeChecker.infer_expr_type({:identifier, "threshold"}, scope) == :float
    end

    test "identifier not in scope returns :any" do
      assert TypeChecker.infer_expr_type({:identifier, "unknown"}, %{}) == :any
    end

    test "AND of two booleans" do
      expr =
        {:binary_op, :and, {:literal, :boolean, true}, {:literal, :boolean, false}}

      assert TypeChecker.infer_expr_type(expr) == :boolean
    end

    test "OR of two booleans" do
      expr =
        {:binary_op, :or, {:literal, :boolean, true}, {:literal, :boolean, false}}

      assert TypeChecker.infer_expr_type(expr) == :boolean
    end

    test "AND with non-boolean operand returns :error" do
      expr =
        {:binary_op, :and, {:literal, :integer, 42}, {:literal, :boolean, true}}

      assert TypeChecker.infer_expr_type(expr) == :error
    end

    test "NOT of boolean" do
      expr = {:unary_op, :not, {:literal, :boolean, true}}
      assert TypeChecker.infer_expr_type(expr) == :boolean
    end

    test "NOT of non-boolean returns :error" do
      expr = {:unary_op, :not, {:literal, :integer, 42}}
      assert TypeChecker.infer_expr_type(expr) == :error
    end

    test "arithmetic on integers" do
      expr = {:binary_op, :add, {:literal, :integer, 1}, {:literal, :integer, 2}}
      assert TypeChecker.infer_expr_type(expr) == :integer
    end

    test "arithmetic on mixed numeric returns float" do
      expr = {:binary_op, :mul, {:literal, :integer, 2}, {:literal, :float, 3.0}}
      assert TypeChecker.infer_expr_type(expr) == :float
    end

    test "arithmetic on non-numeric returns :error" do
      expr =
        {:binary_op, :add, {:literal, :string, "a"}, {:literal, :integer, 1}}

      assert TypeChecker.infer_expr_type(expr) == :error
    end

    test "string concatenation via add" do
      expr =
        {:binary_op, :add, {:literal, :string, "hello "}, {:literal, :string, "world"}}

      assert TypeChecker.infer_expr_type(expr) == :string
    end

    test "comparison returns boolean" do
      expr =
        {:comparison, :gt, {:literal, :integer, 10}, {:literal, :integer, 5}}

      assert TypeChecker.infer_expr_type(expr) == :boolean
    end

    test "comparison of mismatched non-numeric types returns :error" do
      expr =
        {:comparison, :eq, {:literal, :string, "a"}, {:literal, :integer, 1}}

      assert TypeChecker.infer_expr_type(expr) == :error
    end

    test "negation of integer" do
      expr = {:unary_op, :neg, {:literal, :integer, 5}}
      assert TypeChecker.infer_expr_type(expr) == :integer
    end

    test "negation of non-numeric returns :error" do
      expr = {:unary_op, :neg, {:literal, :string, "x"}}
      assert TypeChecker.infer_expr_type(expr) == :error
    end

    test "interpolated string" do
      expr = {:interpolated_string, [{:string, "hello"}, {:expr, []}]}
      assert TypeChecker.infer_expr_type(expr) == :string
    end

    test "module call returns :any" do
      expr = {:module_call, ["Firewall", "block"], [{:literal, :ip_address, "10.0.0.1"}]}
      assert TypeChecker.infer_expr_type(expr) == :any
    end
  end

  # ------------------------------------------------------------------
  # Full Program Checking
  # ------------------------------------------------------------------

  describe "check/1" do
    test "valid program with boolean condition passes" do
      program = [
        AST.policy(
          "allow_traffic",
          {:comparison, :eq, {:identifier, "source"}, {:literal, :string, "trusted"}},
          AST.accept("Trusted source"),
          AST.metadata(priority: 100)
        )
      ]

      assert TypeChecker.check(program) == :ok
    end

    test "policy with non-boolean condition fails" do
      program = [
        AST.policy(
          "bad_policy",
          {:literal, :integer, 42},
          AST.accept(),
          AST.metadata(priority: 10)
        )
      ]

      assert {:error, errors} = TypeChecker.check(program)
      assert length(errors) > 0

      assert Enum.any?(errors, fn e ->
               String.contains?(e.message, "expected boolean condition")
             end)
    end

    test "valid constant declaration passes" do
      program = [
        AST.const_decl("threshold", {:literal, :float, 0.75})
      ]

      assert TypeChecker.check(program) == :ok
    end

    test "import passes" do
      program = [
        AST.import_decl(["Firewall", "Rules"])
      ]

      assert TypeChecker.check(program) == :ok
    end

    test "conditional action with non-boolean IF fails" do
      program = [
        AST.policy(
          "cond_policy",
          {:literal, :boolean, true},
          AST.conditional(
            {:literal, :string, "not a bool"},
            AST.accept(),
            AST.reject()
          ),
          AST.metadata(priority: 50)
        )
      ]

      assert {:error, errors} = TypeChecker.check(program)
      assert length(errors) > 0
    end

    test "block action with well-typed contents passes" do
      program = [
        AST.policy(
          "block_policy",
          {:literal, :boolean, true},
          AST.block([
            AST.report({:literal, :string, "logging"}),
            AST.accept({:literal, :string, "ok"})
          ]),
          AST.metadata(priority: 10)
        )
      ]

      assert TypeChecker.check(program) == :ok
    end

    test "REPORT with non-string message produces error" do
      program = [
        AST.policy(
          "report_policy",
          {:literal, :boolean, true},
          AST.report({:literal, :integer, 42}),
          AST.metadata(priority: 10)
        )
      ]

      assert {:error, errors} = TypeChecker.check(program)

      assert Enum.any?(errors, fn e ->
               String.contains?(e.message, "REPORT message should be a string")
             end)
    end

    test "AND condition with booleans passes" do
      program = [
        AST.policy(
          "and_policy",
          {:binary_op, :and, {:literal, :boolean, true}, {:literal, :boolean, false}},
          AST.reject(),
          AST.metadata(priority: 20)
        )
      ]

      assert TypeChecker.check(program) == :ok
    end

    test "nested NOT condition passes" do
      program = [
        AST.policy(
          "not_policy",
          {:unary_op, :not, {:literal, :boolean, true}},
          AST.reject(),
          AST.metadata(priority: 5)
        )
      ]

      assert TypeChecker.check(program) == :ok
    end

    test "constant in scope is used for condition type checking" do
      program = [
        AST.const_decl("is_enabled", {:literal, :boolean, true}),
        AST.policy(
          "use_const",
          {:identifier, "is_enabled"},
          AST.accept(),
          AST.metadata(priority: 10)
        )
      ]

      assert TypeChecker.check(program) == :ok
    end

    test "integer constant used as condition fails" do
      program = [
        AST.const_decl("port", {:literal, :integer, 8080}),
        AST.policy(
          "use_int_const",
          {:identifier, "port"},
          AST.accept(),
          AST.metadata(priority: 10)
        )
      ]

      assert {:error, errors} = TypeChecker.check(program)
      assert length(errors) > 0
    end

    test "negative priority produces error" do
      program = [
        AST.policy(
          "neg_prio",
          {:literal, :boolean, true},
          AST.accept(),
          %{priority: -5, expires: :never, created_by: nil}
        )
      ]

      assert {:error, errors} = TypeChecker.check(program)

      assert Enum.any?(errors, fn e ->
               String.contains?(e.message, "non-negative integer")
             end)
    end
  end
end
