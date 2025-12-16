# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.ParserTest do
  use ExUnit.Case

  alias Phronesis.{Lexer, Parser}

  defp parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source) do
      Parser.parse(tokens)
    end
  end

  describe "parse/1 - constants" do
    test "parses integer constant" do
      assert {:ok, [{:const, "x", {:literal, :integer, 42}}]} = parse("CONST x = 42")
    end

    test "parses float constant" do
      assert {:ok, [{:const, "pi", {:literal, :float, 3.14}}]} = parse("CONST pi = 3.14")
    end

    test "parses string constant" do
      assert {:ok, [{:const, "msg", {:literal, :string, "hello"}}]} =
               parse(~s(CONST msg = "hello"))
    end

    test "parses boolean constants" do
      assert {:ok, [{:const, "yes", {:literal, :boolean, true}}]} = parse("CONST yes = true")
      assert {:ok, [{:const, "no", {:literal, :boolean, false}}]} = parse("CONST no = false")
    end

    test "parses expression constant" do
      {:ok, [{:const, "sum", expr}]} = parse("CONST sum = 1 + 2 * 3")
      # Should be 1 + (2 * 3) due to precedence
      assert {:binary_op, :add, {:literal, :integer, 1}, {:binary_op, :mul, _, _}} = expr
    end
  end

  describe "parse/1 - imports" do
    test "parses simple import" do
      assert {:ok, [{:import, ["Std", "RPKI"], nil}]} = parse("IMPORT Std.RPKI")
    end

    test "parses import with alias" do
      assert {:ok, [{:import, ["Std", "BGP"], "B"}]} = parse("IMPORT Std.BGP AS B")
    end

    test "parses nested module path" do
      assert {:ok, [{:import, ["Std", "Network", "Routing"], nil}]} =
               parse("IMPORT Std.Network.Routing")
    end
  end

  describe "parse/1 - policies" do
    test "parses simple policy" do
      source = """
      POLICY test_policy:
        x == 1
        THEN REJECT()
        PRIORITY: 100
      """

      {:ok, [{:policy, "test_policy", condition, action, metadata}]} = parse(source)

      assert {:comparison, :eq, {:identifier, "x"}, {:literal, :integer, 1}} = condition
      assert {:reject, nil} = action
      assert %{priority: 100, expires: :never, created_by: nil} = metadata
    end

    test "parses policy with all metadata" do
      source = """
      POLICY full_policy:
        true
        THEN ACCEPT()
        PRIORITY: 200
        EXPIRES: never
        CREATED_BY: admin
      """

      {:ok, [{:policy, "full_policy", _, _, metadata}]} = parse(source)

      assert %{priority: 200, expires: :never, created_by: "admin"} = metadata
    end

    test "parses policy with datetime expiry" do
      source = """
      POLICY temp_policy:
        true
        THEN ACCEPT()
        PRIORITY: 50
        EXPIRES: 2025-12-31T23:59:59Z
      """

      {:ok, [{:policy, _, _, _, metadata}]} = parse(source)
      assert metadata.expires == "2025-12-31T23:59:59Z"
    end
  end

  describe "parse/1 - expressions" do
    test "parses comparison expressions" do
      {:ok, [{:const, _, expr}]} = parse("CONST a = x == 1")
      assert {:comparison, :eq, _, _} = expr

      {:ok, [{:const, _, expr}]} = parse("CONST b = x != 1")
      assert {:comparison, :neq, _, _} = expr

      {:ok, [{:const, _, expr}]} = parse("CONST c = x > 1")
      assert {:comparison, :gt, _, _} = expr
    end

    test "parses logical expressions" do
      {:ok, [{:const, _, expr}]} = parse("CONST a = x == 1 AND y == 2")
      assert {:binary_op, :and, _, _} = expr

      {:ok, [{:const, _, expr}]} = parse("CONST b = x == 1 OR y == 2")
      assert {:binary_op, :or, _, _} = expr
    end

    test "parses NOT expressions" do
      {:ok, [{:const, _, expr}]} = parse("CONST a = NOT x == 1")
      assert {:unary_op, :not, _} = expr
    end

    test "parses parenthesized expressions" do
      {:ok, [{:const, _, expr}]} = parse("CONST a = (1 + 2) * 3")
      assert {:binary_op, :mul, {:binary_op, :add, _, _}, _} = expr
    end

    test "parses module calls" do
      {:ok, [{:const, _, expr}]} = parse("CONST a = Std.RPKI.validate(route)")
      assert {:module_call, ["Std", "RPKI", "validate"], [{:identifier, "route"}]} = expr
    end

    test "parses module calls with multiple args" do
      {:ok, [{:const, _, expr}]} = parse("CONST a = Std.Func.call(x, y, z)")
      assert {:module_call, _, args} = expr
      assert length(args) == 3
    end

    test "parses named arguments" do
      {:ok, [{:const, _, expr}]} = parse("CONST a = Std.Consensus.vote(action, threshold: 0.75)")
      assert {:module_call, _, [_, {:named_arg, "threshold", _}]} = expr
    end
  end

  describe "parse/1 - actions" do
    test "parses EXECUTE action" do
      source = """
      POLICY p:
        true
        THEN EXECUTE(my_func)
        PRIORITY: 1
      """

      {:ok, [{:policy, _, _, action, _}]} = parse(source)
      assert {:execute, "my_func", []} = action
    end

    test "parses EXECUTE with args" do
      source = """
      POLICY p:
        true
        THEN EXECUTE(set_pref, 100)
        PRIORITY: 1
      """

      {:ok, [{:policy, _, _, action, _}]} = parse(source)
      assert {:execute, "set_pref", [{:literal, :integer, 100}]} = action
    end

    test "parses REPORT action" do
      source = """
      POLICY p:
        true
        THEN REPORT("message")
        PRIORITY: 1
      """

      {:ok, [{:policy, _, _, action, _}]} = parse(source)
      assert {:report, {:literal, :string, "message"}} = action
    end

    test "parses REJECT action" do
      source = """
      POLICY p:
        true
        THEN REJECT("reason")
        PRIORITY: 1
      """

      {:ok, [{:policy, _, _, action, _}]} = parse(source)
      assert {:reject, {:literal, :string, "reason"}} = action
    end

    test "parses ACCEPT action" do
      source = """
      POLICY p:
        true
        THEN ACCEPT()
        PRIORITY: 1
      """

      {:ok, [{:policy, _, _, action, _}]} = parse(source)
      assert {:accept, nil} = action
    end

    test "parses compound action (BEGIN...END)" do
      source = """
      POLICY p:
        true
        THEN BEGIN
          REPORT("first")
          REPORT("second")
        END
        PRIORITY: 1
      """

      {:ok, [{:policy, _, _, action, _}]} = parse(source)
      assert {:block, [_, _]} = action
    end

    test "parses conditional action" do
      source = """
      POLICY p:
        true
        THEN IF x == 1 THEN ACCEPT() ELSE REJECT()
        PRIORITY: 1
      """

      {:ok, [{:policy, _, _, action, _}]} = parse(source)
      assert {:conditional, _, {:accept, nil}, {:reject, nil}} = action
    end
  end

  describe "parse/1 - multiple declarations" do
    test "parses multiple declarations" do
      source = """
      IMPORT Std.RPKI
      CONST threshold = 0.75
      POLICY test:
        true
        THEN ACCEPT()
        PRIORITY: 1
      """

      {:ok, decls} = parse(source)
      assert length(decls) == 3
      assert {:import, _, _} = Enum.at(decls, 0)
      assert {:const, _, _} = Enum.at(decls, 1)
      assert {:policy, _, _, _, _} = Enum.at(decls, 2)
    end
  end

  describe "parse/1 - error handling" do
    test "returns error for unexpected token" do
      assert {:error, {:parse_error, _, _, _}} = parse("INVALID")
    end

    test "returns error for missing identifier" do
      assert {:error, {:parse_error, "expected identifier", _, _}} = parse("CONST = 1")
    end

    test "returns error for missing colon in policy" do
      assert {:error, {:parse_error, _, _, _}} = parse("POLICY test true THEN ACCEPT()")
    end
  end
end
