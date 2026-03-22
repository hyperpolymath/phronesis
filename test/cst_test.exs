# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Phronesis Contributors

defmodule Phronesis.CSTTest do
  use ExUnit.Case, async: true

  alias Phronesis.CST

  describe "round-trip source preservation" do
    test "simple constant declaration" do
      source = "CONST x = 42"
      cst = CST.parse_to_cst(source)
      assert CST.to_source(cst) == source
    end

    test "with line comment" do
      source = "# this is a comment\nCONST x = 42"
      cst = CST.parse_to_cst(source)
      assert CST.to_source(cst) == source
    end

    test "with extra whitespace" do
      source = "  CONST  x  =  42  "
      cst = CST.parse_to_cst(source)
      assert CST.to_source(cst) == source
    end

    test "multiline with blank lines" do
      source = "# Header\n\nCONST x = 1\nCONST y = 2\n"
      cst = CST.parse_to_cst(source)
      assert CST.to_source(cst) == source
    end

    test "empty source" do
      cst = CST.parse_to_cst("")
      assert CST.to_source(cst) == ""
    end

    test "whitespace only" do
      source = "   \n\n  \t  "
      cst = CST.parse_to_cst(source)
      assert CST.to_source(cst) == source
    end

    test "operators and comparisons" do
      source = "CONST x = 1 + 2 * 3"
      cst = CST.parse_to_cst(source)
      assert CST.to_source(cst) == source
    end

    test "policy declaration" do
      source = "POLICY test_policy\n  src.ip == 10.0.0.1\nTHEN ACCEPT"
      cst = CST.parse_to_cst(source)
      assert CST.to_source(cst) == source
    end
  end

  describe "trivia preservation" do
    test "line comment is captured as leading trivia" do
      source = "# comment\nCONST x = 42"
      cst = CST.parse_to_cst(source)
      toks = CST.tokens(cst)

      # Find the CONST token
      const_tok = Enum.find(toks, fn tok -> tok.kind == :const end)

      assert const_tok != nil
      has_comment = Enum.any?(const_tok.leading_trivia, fn t -> t.kind == :line_comment end)
      assert has_comment, "CONST token should have leading line comment trivia"
    end

    test "whitespace is captured as trivia" do
      source = "   CONST x = 42"
      cst = CST.parse_to_cst(source)
      toks = CST.tokens(cst)
      first_tok = List.first(toks)
      has_ws = Enum.any?(first_tok.leading_trivia, fn t -> t.kind == :whitespace end)
      assert has_ws, "first token should have leading whitespace trivia"
    end
  end

  describe "token collection" do
    test "tokens in document order" do
      source = "CONST x = 1"
      cst = CST.parse_to_cst(source)
      toks = CST.tokens(cst)
      texts = Enum.map(toks, fn tok -> tok.text end)
      # Filter out EOF if present
      texts = Enum.reject(texts, fn t -> t == "" end)
      assert texts == ["CONST", "x", "=", "1"]
    end
  end
end
