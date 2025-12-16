# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule PhronesisTest do
  use ExUnit.Case
  doctest Phronesis

  describe "parse/1" do
    test "parses constant declaration" do
      assert {:ok, [{:const, "x", {:literal, :integer, 42}}]} =
               Phronesis.parse("CONST x = 42")
    end

    test "parses string constant" do
      assert {:ok, [{:const, "msg", {:literal, :string, "hello"}}]} =
               Phronesis.parse(~s(CONST msg = "hello"))
    end

    test "parses boolean constants" do
      assert {:ok, [{:const, "flag", {:literal, :boolean, true}}]} =
               Phronesis.parse("CONST flag = true")
    end

    test "parses arithmetic expressions" do
      assert {:ok, [{:const, "sum", {:binary_op, :add, _, _}}]} =
               Phronesis.parse("CONST sum = 1 + 2")
    end

    test "parses import declaration" do
      assert {:ok, [{:import, ["Std", "RPKI"], nil}]} =
               Phronesis.parse("IMPORT Std.RPKI")
    end

    test "parses import with alias" do
      assert {:ok, [{:import, ["Std", "RPKI"], "R"}]} =
               Phronesis.parse("IMPORT Std.RPKI AS R")
    end
  end

  describe "tokenize/1" do
    test "tokenizes keywords" do
      {:ok, tokens} = Phronesis.tokenize("POLICY THEN AND OR")

      types = Enum.map(tokens, fn {type, _, _, _} -> type end)
      assert [:policy, :then, :and, :or, :eof] = types
    end

    test "tokenizes operators" do
      {:ok, tokens} = Phronesis.tokenize("== != > >= < <=")

      types = Enum.map(tokens, fn {type, _, _, _} -> type end)
      assert [:eq, :neq, :gt, :gte, :lt, :lte, :eof] = types
    end

    test "tokenizes IP addresses" do
      {:ok, tokens} = Phronesis.tokenize("192.168.1.1")
      assert [{:ip_address, "192.168.1.1", _, _}, {:eof, _, _, _}] = tokens
    end

    test "tokenizes IP with CIDR" do
      {:ok, tokens} = Phronesis.tokenize("10.0.0.0/8")
      assert [{:ip_address, "10.0.0.0/8", _, _}, {:eof, _, _, _}] = tokens
    end

    test "skips comments" do
      {:ok, tokens} = Phronesis.tokenize("CONST x = 1 # comment\nCONST y = 2")

      values =
        tokens
        |> Enum.filter(fn {type, _, _, _} -> type == :identifier end)
        |> Enum.map(fn {_, val, _, _} -> val end)

      assert ["x", "y"] = values
    end
  end
end
