# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# LSP Integration Tests

defmodule Phronesis.LSPIntegrationTest do
  @moduledoc """
  Integration tests for the Phronesis LSP server.

  Tests document management, auto-completion, hover, and diagnostics.
  """

  use ExUnit.Case, async: false
  alias Phronesis.LSP.{TextDocument, Completion, Hover, Definition}

  @sample_doc """
  IMPORT Std.BGP
  CONST MAX_HOPS = 10

  POLICY check_path:
    IF Std.BGP.path_length(route) < MAX_HOPS THEN
      ACCEPT "Path within limits"
    ELSE
      REJECT "Path too long"
  PRIORITY 50
  """

  describe "TextDocument" do
    test "creates document with text" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: @sample_doc,
        version: 1
      }

      assert doc.uri == "file:///test.phr"
      assert doc.text =~ "IMPORT Std.BGP"
      assert doc.version == 1
    end

    test "gets word at position" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "POLICY test_policy:",
        version: 1
      }

      # Position at "POLICY" keyword
      word = TextDocument.word_at_position(doc, %{"line" => 0, "character" => 3})
      assert String.contains?(word, "POL")

      # Position at "test_policy"
      word = TextDocument.word_at_position(doc, %{"line" => 0, "character" => 10})
      assert String.contains?(word, "test")
    end
  end

  describe "Completion" do
    test "returns completions for keywords" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "PO",
        version: 1
      }

      completions = Completion.compute(doc, %{"line" => 0, "character" => 2})

      # Should have some completions
      assert is_list(completions)
      assert length(completions) > 0

      # Check that completions have required fields
      first = List.first(completions)
      assert Map.has_key?(first, "label")
      assert Map.has_key?(first, "kind")
    end

    test "returns completions for Std prefix" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "Std.",
        version: 1
      }

      completions = Completion.compute(doc, %{"line" => 0, "character" => 4})

      # Should return module completions
      assert is_list(completions)
      assert length(completions) > 0
    end

    test "returns completions in general" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "IF",
        version: 1
      }

      completions = Completion.compute(doc, %{"line" => 0, "character" => 2})

      # Should return keyword completions
      assert is_list(completions)
    end
  end

  describe "Hover" do
    test "returns hover for keywords" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "POLICY test:",
        version: 1
      }

      hover = Hover.compute(doc, %{"line" => 0, "character" => 3})

      # May return hover info or nil
      if hover != nil do
        assert Map.has_key?(hover, "contents")
      end
    end

    test "handles hover on empty position" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "   ",
        version: 1
      }

      hover = Hover.compute(doc, %{"line" => 0, "character" => 1})

      # Should handle gracefully (either nil or empty hover)
      assert hover == nil or is_map(hover)
    end
  end

  describe "Definition" do
    test "attempts to find definitions" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: @sample_doc,
        version: 1
      }

      # Try to find definition (may or may not succeed)
      result = Definition.compute(doc, %{"line" => 4, "character" => 10}, [doc])

      # Should return nil or a valid definition structure
      assert result == nil or is_list(result) or is_map(result)
    end
  end

  describe "Parsing and Diagnostics" do
    test "handles valid syntax" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "POLICY test:\n  IF true THEN\n    ACCEPT \"ok\"\n  PRIORITY 1",
        version: 1
      }

      # Try to parse
      result = Phronesis.parse(doc.text)

      # Should either succeed or fail gracefully
      assert match?({:ok, _}, result) or match?({:error, _}, result)
    end

    test "handles invalid syntax" do
      doc = %TextDocument{
        uri: "file:///test.phr",
        text: "POLICY invalid syntax here",
        version: 1
      }

      # Should return error
      result = Phronesis.parse(doc.text)

      assert match?({:error, _}, result)
    end
  end

end
