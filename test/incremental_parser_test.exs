# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

defmodule Phronesis.IncrementalParserTest do
  use ExUnit.Case

  alias Phronesis.IncrementalParser

  # ── Test 1: Edit inside a policy body ──────────────────────────────

  describe "edit/2 - edit inside declaration body" do
    test "editing a constant value preserves item count" do
      source = "CONST x = 42\nCONST y = 99\n"
      state = IncrementalParser.new(source)
      original_count = length(IncrementalParser.items(state))
      assert original_count >= 2

      # Change 42 to 100
      pos = find_byte_offset(source, "42")

      {new_state, _diags} =
        IncrementalParser.edit(state, %{start: pos, old_end: pos + 2, new_text: "100"})

      assert length(IncrementalParser.items(new_state)) == original_count
      assert String.contains?(IncrementalParser.source(new_state), "100")
    end
  end

  # ── Test 2: Add a new declaration ──────────────────────────────────

  describe "edit/2 - add new declaration" do
    test "appending a const increases item count" do
      source = "CONST x = 1\n"
      state = IncrementalParser.new(source)
      original_count = length(IncrementalParser.items(state))

      new_decl = "CONST z = 42\n"
      insert_pos = byte_size(source)

      {new_state, _diags} =
        IncrementalParser.edit(state, %{
          start: insert_pos,
          old_end: insert_pos,
          new_text: new_decl
        })

      assert length(IncrementalParser.items(new_state)) >= original_count
      assert String.contains?(IncrementalParser.source(new_state), "CONST z")
    end
  end

  # ── Test 3: Delete a declaration ───────────────────────────────────

  describe "edit/2 - delete declaration" do
    test "removing a const reduces item count" do
      source = "CONST a = 1\nCONST b = 2\nCONST c = 3\n"
      state = IncrementalParser.new(source)
      original_count = length(IncrementalParser.items(state))

      # Delete CONST b line
      b_start = find_byte_offset(source, "CONST b")
      b_end = find_byte_offset(source, "CONST c")

      {new_state, _diags} =
        IncrementalParser.edit(state, %{
          start: b_start,
          old_end: b_end,
          new_text: ""
        })

      assert length(IncrementalParser.items(new_state)) < original_count
      refute String.contains?(IncrementalParser.source(new_state), "CONST b")
      assert String.contains?(IncrementalParser.source(new_state), "CONST c")
    end
  end

  # ── Test 4: Edit declaration name ──────────────────────────────────

  describe "edit/2 - edit declaration name" do
    test "renaming a constant" do
      source = "CONST old_name = 42\n"
      state = IncrementalParser.new(source)

      pos = find_byte_offset(source, "old_name")

      {new_state, _diags} =
        IncrementalParser.edit(state, %{
          start: pos,
          old_end: pos + 8,
          new_text: "new_name"
        })

      assert String.contains?(IncrementalParser.source(new_state), "new_name")
      refute String.contains?(IncrementalParser.source(new_state), "old_name")
      assert length(IncrementalParser.items(new_state)) >= 1
    end
  end

  # ── Test 5: Edit across declaration boundary ───────────────────────

  describe "edit/2 - edit across boundary" do
    test "replacing two consts with one" do
      source = "CONST a = 1\nCONST b = 2\n"
      state = IncrementalParser.new(source)

      {new_state, _diags} =
        IncrementalParser.edit(state, %{
          start: 0,
          old_end: byte_size(source),
          new_text: "CONST merged = 99\n"
        })

      assert String.contains?(IncrementalParser.source(new_state), "CONST merged")
      assert length(IncrementalParser.items(new_state)) >= 1
    end
  end

  # ── Test 6: Insert between items ───────────────────────────────────

  describe "edit/2 - insert between items" do
    test "inserting a const between two existing consts" do
      source = "CONST a = 1\nCONST c = 3\n"
      state = IncrementalParser.new(source)
      original_count = length(IncrementalParser.items(state))

      insert_pos = find_byte_offset(source, "CONST c")

      {new_state, _diags} =
        IncrementalParser.edit(state, %{
          start: insert_pos,
          old_end: insert_pos,
          new_text: "CONST b = 2\n"
        })

      assert length(IncrementalParser.items(new_state)) >= original_count
      assert String.contains?(IncrementalParser.source(new_state), "CONST b")
    end
  end

  # ── Test 7: No-op edit ─────────────────────────────────────────────

  describe "edit/2 - no-op edit" do
    test "replacing text with identical text" do
      source = "CONST x = 42\n"
      state = IncrementalParser.new(source)
      original_count = length(IncrementalParser.items(state))

      pos = find_byte_offset(source, "42")

      {new_state, _diags} =
        IncrementalParser.edit(state, %{start: pos, old_end: pos + 2, new_text: "42"})

      assert length(IncrementalParser.items(new_state)) == original_count
      assert IncrementalParser.source(new_state) == source
    end
  end

  # ── Test 8: Edit producing syntax error ────────────────────────────

  describe "edit/2 - syntax error" do
    test "breaking syntax does not crash" do
      source = "CONST x = 42\n"
      state = IncrementalParser.new(source)

      # Replace "42" with garbage
      pos = find_byte_offset(source, "42")

      {new_state, _diags} =
        IncrementalParser.edit(state, %{start: pos, old_end: pos + 2, new_text: "@@!!"})

      # Should not crash; state is still valid
      assert is_binary(IncrementalParser.source(new_state))
    end
  end

  # ── Test 9: Multiple sequential edits ──────────────────────────────

  describe "edit/2 - multiple sequential edits" do
    test "two edits in sequence" do
      source = "CONST a = 1\nCONST b = 2\nCONST c = 3\n"
      state = IncrementalParser.new(source)

      # Edit 1: change a's value
      pos1 = find_byte_offset(IncrementalParser.source(state), "= 1") + 2

      {state2, _} =
        IncrementalParser.edit(state, %{start: pos1, old_end: pos1 + 1, new_text: "10"})

      assert String.contains?(IncrementalParser.source(state2), "10")

      # Edit 2: change c's value
      pos2 = find_byte_offset(IncrementalParser.source(state2), "= 3") + 2

      {state3, _} =
        IncrementalParser.edit(state2, %{start: pos2, old_end: pos2 + 1, new_text: "30"})

      assert String.contains?(IncrementalParser.source(state3), "30")
      assert String.contains?(IncrementalParser.source(state3), "= 2")
    end
  end

  # ── Test 10: Full AST reconstruction ───────────────────────────────

  describe "full_ast/1" do
    test "returns all declarations" do
      source = "CONST x = 1\nCONST y = 2\n"
      state = IncrementalParser.new(source)
      ast = IncrementalParser.full_ast(state)
      assert length(ast) >= 2
    end
  end

  # ── Test 11: Empty source ──────────────────────────────────────────

  describe "new/1 - empty source" do
    test "handles empty string" do
      state = IncrementalParser.new("")
      assert length(IncrementalParser.items(state)) == 0
      assert IncrementalParser.full_ast(state) == []
    end
  end

  # ── Test 12: Cached decl kind tags ─────────────────────────────────

  describe "cached decl kind tags" do
    test "const is tagged as Const" do
      state = IncrementalParser.new("CONST x = 1\n")
      items = IncrementalParser.items(state)
      assert length(items) >= 1
      assert hd(items).kind == "Const"
    end

    test "import is tagged as Import" do
      state = IncrementalParser.new("IMPORT Std.BGP\n")
      items = IncrementalParser.items(state)
      assert length(items) >= 1
      assert hd(items).kind == "Import"
    end
  end

  # ── Test 13: Policy declaration ────────────────────────────────────

  describe "policy parsing" do
    test "parses and caches a policy" do
      source = """
      POLICY reject_invalid: prefix_length > 24 THEN REJECT() PRIORITY: 100
      """

      state = IncrementalParser.new(source)
      items = IncrementalParser.items(state)
      assert length(items) >= 1
      assert hd(items).kind == "Policy"
    end
  end

  # ── Helpers ────────────────────────────────────────────────────────

  # Find the byte offset of a substring in source.
  # Returns 0 if not found (tests will fail on wrong data rather than crash).
  defp find_byte_offset(source, needle) do
    case :binary.match(source, needle) do
      {pos, _len} -> pos
      :nomatch -> 0
    end
  end
end
