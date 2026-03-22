# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

defmodule Phronesis.IncrementalLexerTest do
  use ExUnit.Case, async: true

  alias Phronesis.IncrementalLexer

  # Helper: get token types from an incremental lexer state (excluding :eof).
  defp token_types(state) do
    IncrementalLexer.token_types(state)
  end

  # Helper: get token types from a fresh full lex (excluding :eof).
  defp fresh_types(source) do
    fresh = IncrementalLexer.create(source)
    IncrementalLexer.token_types(fresh)
  end

  # Helper: assert incremental result matches a full re-lex.
  defp assert_matches(state) do
    inc = token_types(state)
    full = fresh_types(IncrementalLexer.source(state))
    assert inc == full,
      "Token type mismatch:\n  incremental: #{inspect(inc)}\n  full:        #{inspect(full)}"
  end

  # ----- Edit in middle of file -----

  test "edit in middle" do
    state = IncrementalLexer.create("CONST x = 42")
    state = IncrementalLexer.edit(state, %{start: 10, old_end: 12, new_text: "99"})
    assert IncrementalLexer.source(state) == "CONST x = 99"
    assert_matches(state)
  end

  # ----- Edit at start -----

  test "edit at start" do
    state = IncrementalLexer.create("CONST x = 5")
    state = IncrementalLexer.edit(state, %{start: 0, old_end: 5, new_text: "POLICY"})
    assert IncrementalLexer.source(state) == "POLICY x = 5"
    assert_matches(state)
  end

  # ----- Edit at end -----

  test "edit at end" do
    state = IncrementalLexer.create("CONST x = 5")
    len = byte_size(IncrementalLexer.source(state))
    state = IncrementalLexer.edit(state, %{start: len, old_end: len, new_text: " AND y"})
    assert IncrementalLexer.source(state) == "CONST x = 5 AND y"
    assert_matches(state)
  end

  # ----- Insert new text -----

  test "insert text" do
    state = IncrementalLexer.create("POLICY myPolicy")
    state = IncrementalLexer.edit(state, %{start: 15, old_end: 15, new_text: " THEN ACCEPT"})
    assert IncrementalLexer.source(state) == "POLICY myPolicy THEN ACCEPT"
    assert_matches(state)
  end

  # ----- Delete text -----

  test "delete text" do
    state = IncrementalLexer.create("CONST x = 10 AND y")
    # Delete " AND y"
    state = IncrementalLexer.edit(state, %{start: 13, old_end: 19, new_text: ""})
    assert IncrementalLexer.source(state) == "CONST x = 10 "
    assert_matches(state)
  end

  # ----- Replace text -----

  test "replace text" do
    state = IncrementalLexer.create("CONST x = 10")
    state = IncrementalLexer.edit(state, %{start: 6, old_end: 12, new_text: "name = 42"})
    assert IncrementalLexer.source(state) == "CONST name = 42"
    assert_matches(state)
  end

  # ----- Edit that changes token boundaries -----

  test "token boundary change: == to =" do
    state = IncrementalLexer.create("x == y")
    state = IncrementalLexer.edit(state, %{start: 2, old_end: 4, new_text: "="})
    assert IncrementalLexer.source(state) == "x = y"
    assert_matches(state)
  end

  test "token boundary expand: = to ==" do
    state = IncrementalLexer.create("x = y")
    state = IncrementalLexer.edit(state, %{start: 2, old_end: 3, new_text: "=="})
    assert IncrementalLexer.source(state) == "x == y"
    assert_matches(state)
  end

  # ----- Edit inside a string literal -----

  test "edit inside string" do
    state = IncrementalLexer.create(~s(CONST s = "hello world"))
    # Change "hello" to "goodbye" inside the string
    state = IncrementalLexer.edit(state, %{start: 11, old_end: 16, new_text: "goodbye"})
    assert IncrementalLexer.source(state) == ~s(CONST s = "goodbye world")
    assert_matches(state)
  end

  # ----- Edit inside a comment -----

  test "edit inside comment" do
    state = IncrementalLexer.create("# old comment\nCONST x = 1")
    state = IncrementalLexer.edit(state, %{start: 2, old_end: 5, new_text: "new"})
    assert IncrementalLexer.source(state) == "# new comment\nCONST x = 1"
    assert_matches(state)
  end

  # ----- Multiple sequential edits -----

  test "multiple edits" do
    state = IncrementalLexer.create("CONST a = 1 AND b")
    # Edit 1
    state = IncrementalLexer.edit(state, %{start: 6, old_end: 7, new_text: "x"})
    assert_matches(state)
    # Edit 2
    state = IncrementalLexer.edit(state, %{start: 16, old_end: 17, new_text: "y"})
    assert IncrementalLexer.source(state) == "CONST x = 1 AND y"
    assert_matches(state)
  end

  # ----- Empty source -----

  test "empty source then insert" do
    state = IncrementalLexer.create("")
    state = IncrementalLexer.edit(state, %{start: 0, old_end: 0, new_text: "CONST x = 1"})
    assert IncrementalLexer.source(state) == "CONST x = 1"
    assert_matches(state)
  end

  # ----- Delete everything -----

  test "delete all" do
    state = IncrementalLexer.create("CONST x = 1")
    len = byte_size(IncrementalLexer.source(state))
    state = IncrementalLexer.edit(state, %{start: 0, old_end: len, new_text: ""})
    assert IncrementalLexer.source(state) == ""
    assert_matches(state)
  end
end
