# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.LexerTest do
  use ExUnit.Case

  alias Phronesis.Lexer

  describe "tokenize/1" do
    test "tokenizes empty input" do
      assert {:ok, [{:eof, nil, 1, 1}]} = Lexer.tokenize("")
    end

    test "tokenizes integers" do
      assert {:ok, [{:integer, 42, 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("42")
      assert {:ok, [{:integer, 0, 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("0")
      assert {:ok, [{:integer, 12345, 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("12345")
    end

    test "tokenizes floats" do
      assert {:ok, [{:float, 3.14, 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("3.14")
      assert {:ok, [{:float, 0.5, 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("0.5")
    end

    test "tokenizes strings" do
      assert {:ok, [{:string, "hello", 1, 1}, {:eof, _, _, _}]} =
               Lexer.tokenize(~s("hello"))

      assert {:ok, [{:string, "with spaces", 1, 1}, {:eof, _, _, _}]} =
               Lexer.tokenize(~s("with spaces"))
    end

    test "tokenizes string escapes" do
      assert {:ok, [{:string, "line1\nline2", 1, 1}, {:eof, _, _, _}]} =
               Lexer.tokenize(~s("line1\\nline2"))

      assert {:ok, [{:string, "tab\there", 1, 1}, {:eof, _, _, _}]} =
               Lexer.tokenize(~s("tab\\there"))
    end

    test "tokenizes all keywords" do
      keywords = ~w(POLICY THEN PRIORITY EXPIRES CREATED_BY CONST AND OR NOT
                    EXECUTE REPORT REJECT ACCEPT IF ELSE BEGIN END IMPORT AS)

      for keyword <- keywords do
        {:ok, tokens} = Lexer.tokenize(keyword)
        [{type, _, _, _} | _] = tokens
        # Keywords should not be :identifier
        assert type != :identifier, "#{keyword} should be recognized as keyword"
      end
    end

    test "tokenizes identifiers" do
      assert {:ok, [{:identifier, "foo", 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("foo")
      assert {:ok, [{:identifier, "my_var", 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("my_var")
      assert {:ok, [{:identifier, "var123", 1, 1}, {:eof, _, _, _}]} = Lexer.tokenize("var123")
    end

    test "tokenizes comparison operators" do
      assert {:ok, [{:eq, "==", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("==")
      assert {:ok, [{:neq, "!=", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("!=")
      assert {:ok, [{:gt, ">", _, _}, {:eof, _, _, _}]} = Lexer.tokenize(">")
      assert {:ok, [{:gte, ">=", _, _}, {:eof, _, _, _}]} = Lexer.tokenize(">=")
      assert {:ok, [{:lt, "<", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("<")
      assert {:ok, [{:lte, "<=", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("<=")
    end

    test "tokenizes arithmetic operators" do
      assert {:ok, [{:plus, "+", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("+")
      assert {:ok, [{:minus, "-", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("-")
      assert {:ok, [{:star, "*", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("*")
      assert {:ok, [{:slash, "/", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("/")
    end

    test "tokenizes delimiters" do
      assert {:ok, [{:lparen, "(", _, _}, {:eof, _, _, _}]} = Lexer.tokenize("(")
      assert {:ok, [{:rparen, ")", _, _}, {:eof, _, _, _}]} = Lexer.tokenize(")")
      assert {:ok, [{:comma, ",", _, _}, {:eof, _, _, _}]} = Lexer.tokenize(",")
      assert {:ok, [{:colon, ":", _, _}, {:eof, _, _, _}]} = Lexer.tokenize(":")
      assert {:ok, [{:dot, ".", _, _}, {:eof, _, _, _}]} = Lexer.tokenize(".")
    end

    test "tracks line numbers" do
      {:ok, tokens} = Lexer.tokenize("a\nb\nc")

      lines = Enum.map(tokens, fn {_, _, line, _} -> line end)
      assert [1, 2, 3, 3] = lines
    end

    test "tracks column numbers" do
      {:ok, tokens} = Lexer.tokenize("abc def ghi")

      columns =
        tokens
        |> Enum.filter(fn {type, _, _, _} -> type == :identifier end)
        |> Enum.map(fn {_, _, _, col} -> col end)

      assert [1, 5, 9] = columns
    end

    test "handles datetime literals" do
      {:ok, tokens} = Lexer.tokenize("2025-12-16T10:30:00Z")
      assert [{:datetime, "2025-12-16T10:30:00Z", _, _}, {:eof, _, _, _}] = tokens
    end

    test "returns error for invalid characters" do
      assert {:error, {:lexer_error, _, 1, 1}} = Lexer.tokenize("@")
      assert {:error, {:lexer_error, _, 1, 1}} = Lexer.tokenize("$")
    end

    test "returns error for unterminated string" do
      assert {:error, {:lexer_error, "unterminated string", 1, 1}} =
               Lexer.tokenize(~s("hello))
    end
  end
end
