# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.DiagnosticsTest do
  use ExUnit.Case, async: true
  alias Phronesis.Diagnostics
  alias Phronesis.Diagnostics.Reporter
  alias Phronesis.Diagnostics.Suggestions

  describe "Diagnostics.new/5" do
    test "creates a diagnostic with all fields" do
      location = %{file: "test.phr", line: 10, column: 5}

      diagnostic =
        Diagnostics.new("E0001", :error, "test error", location,
          context: "some context",
          suggestion: "try this",
          help: "helpful info"
        )

      assert diagnostic.code == "E0001"
      assert diagnostic.severity == :error
      assert diagnostic.message == "test error"
      assert diagnostic.location == location
      assert diagnostic.context == "some context"
      assert diagnostic.suggestion == "try this"
      assert diagnostic.help == "helpful info"
    end

    test "creates a diagnostic with minimal fields" do
      location = %{file: "test.phr", line: 10, column: 5}
      diagnostic = Diagnostics.new("W0100", :warning, "test warning", location)

      assert diagnostic.code == "W0100"
      assert diagnostic.severity == :warning
      assert diagnostic.message == "test warning"
      assert diagnostic.context == nil
      assert diagnostic.suggestion == nil
      assert diagnostic.help == nil
    end
  end

  describe "Diagnostics.format/2" do
    test "formats a simple error" do
      location = %{file: "test.phr", line: 10, column: 5}
      diagnostic = Diagnostics.new("E0001", :error, "test error", location)

      formatted = Diagnostics.format(diagnostic, color: false)

      assert formatted =~ "error[E0001]: test error"
      assert formatted =~ "--> test.phr:10:5"
    end

    test "formats an error with context" do
      location = %{file: "test.phr", line: 10, column: 5}

      diagnostic =
        Diagnostics.new("E0042", :error, "undefined variable 'foo'", location,
          context: "  foo > 50"
        )

      formatted = Diagnostics.format(diagnostic, color: false)

      assert formatted =~ "error[E0042]: undefined variable 'foo'"
      assert formatted =~ "--> test.phr:10:5"
      assert formatted =~ "foo > 50"
      assert formatted =~ "^ not found in this scope"
    end

    test "formats an error with suggestion" do
      location = %{file: "test.phr", line: 10, column: 5}

      diagnostic =
        Diagnostics.new("E0042", :error, "undefined variable 'foo'", location,
          suggestion: "Did you mean 'bar'?"
        )

      formatted = Diagnostics.format(diagnostic, color: false)

      assert formatted =~ "help: Did you mean 'bar'?"
    end

    test "formats an error with help text" do
      location = %{file: "test.phr", line: 10, column: 5}

      diagnostic =
        Diagnostics.new("E0001", :error, "test error", location,
          help: "This is helpful information"
        )

      formatted = Diagnostics.format(diagnostic, color: false)

      assert formatted =~ "note: This is helpful information"
    end
  end

  describe "Diagnostics helper functions" do
    test "lexer_error creates proper diagnostic" do
      diagnostic = Diagnostics.lexer_error("unexpected token", "test.phr", 5, 10)

      assert diagnostic.code == "E0001"
      assert diagnostic.severity == :error
      assert diagnostic.message == "unexpected token"
      assert diagnostic.location.line == 5
      assert diagnostic.location.column == 10
      assert diagnostic.help =~ "syntax"
    end

    test "parser_error creates proper diagnostic" do
      diagnostic = Diagnostics.parser_error("expected THEN", "test.phr", 8, 3)

      assert diagnostic.code == "E0002"
      assert diagnostic.severity == :error
      assert diagnostic.message == "expected THEN"
      assert diagnostic.location.line == 8
      assert diagnostic.help =~ "syntax structure"
    end

    test "undefined_variable creates proper diagnostic" do
      diagnostic = Diagnostics.undefined_variable("risk_levle", "test.phr", 12, 3)

      assert diagnostic.code == "E0042"
      assert diagnostic.severity == :error
      assert diagnostic.message =~ "undefined variable 'risk_levle'"
      assert diagnostic.location.line == 12
    end

    test "undefined_variable with suggestion" do
      diagnostic =
        Diagnostics.undefined_variable("risk_levle", "test.phr", 12, 3, similar: "risk_level")

      assert diagnostic.suggestion == "Did you mean 'risk_level'?"
    end

    test "undefined_constant creates proper diagnostic" do
      diagnostic = Diagnostics.undefined_constant("MAX_VALU", "test.phr", 5, 10)

      assert diagnostic.code == "E0043"
      assert diagnostic.severity == :error
      assert diagnostic.message =~ "undefined constant 'MAX_VALU'"
    end

    test "type_error creates proper diagnostic" do
      diagnostic = Diagnostics.type_error("integer", "string", "test.phr", 15, 7)

      assert diagnostic.code == "E0100"
      assert diagnostic.severity == :error
      assert diagnostic.message =~ "type mismatch"
      assert diagnostic.message =~ "expected integer"
      assert diagnostic.message =~ "got string"
    end

    test "invalid_threshold creates proper warning" do
      diagnostic = Diagnostics.invalid_threshold(1.5, "test.phr", 3, 20)

      assert diagnostic.code == "W0200"
      assert diagnostic.severity == :warning
      assert diagnostic.message =~ "consensus threshold"
      assert diagnostic.message =~ "1.5"
    end

    test "dead_code creates proper warning" do
      diagnostic = Diagnostics.dead_code("never_matches", "test.phr", 20, 1)

      assert diagnostic.code == "W0300"
      assert diagnostic.severity == :warning
      assert diagnostic.message =~ "unreachable condition"
      assert diagnostic.message =~ "never_matches"
    end

    test "unused_import creates proper warning" do
      diagnostic = Diagnostics.unused_import("Std.Temporal", "test.phr", 1, 1)

      assert diagnostic.code == "W0400"
      assert diagnostic.severity == :warning
      assert diagnostic.message =~ "unused import"
      assert diagnostic.message =~ "Std.Temporal"
    end
  end

  describe "Reporter.new/1" do
    test "creates an empty report" do
      report = Reporter.new("test.phr")

      assert report.file == "test.phr"
      assert report.diagnostics == []
      assert report.error_count == 0
      assert report.warning_count == 0
      assert report.info_count == 0
    end
  end

  describe "Reporter.add/2" do
    test "adds a diagnostic and increments error count" do
      report = Reporter.new("test.phr")
      location = %{file: "test.phr", line: 1, column: 1}
      diagnostic = Diagnostics.new("E0001", :error, "test", location)

      updated = Reporter.add(report, diagnostic)

      assert length(updated.diagnostics) == 1
      assert updated.error_count == 1
      assert updated.warning_count == 0
    end

    test "adds a diagnostic and increments warning count" do
      report = Reporter.new("test.phr")
      location = %{file: "test.phr", line: 1, column: 1}
      diagnostic = Diagnostics.new("W0100", :warning, "test", location)

      updated = Reporter.add(report, diagnostic)

      assert length(updated.diagnostics) == 1
      assert updated.error_count == 0
      assert updated.warning_count == 1
    end
  end

  describe "Reporter.has_errors?/1" do
    test "returns true when there are errors" do
      report = Reporter.new("test.phr")
      location = %{file: "test.phr", line: 1, column: 1}
      diagnostic = Diagnostics.new("E0001", :error, "test", location)
      updated = Reporter.add(report, diagnostic)

      assert Reporter.has_errors?(updated) == true
    end

    test "returns false when there are no errors" do
      report = Reporter.new("test.phr")

      assert Reporter.has_errors?(report) == false
    end
  end

  describe "Reporter.format_summary/2" do
    test "formats summary with no issues" do
      report = Reporter.new("test.phr")
      summary = Reporter.format_summary(report, false)

      assert summary =~ "No issues found"
    end

    test "formats summary with errors only" do
      report = %{
        Reporter.new("test.phr")
        | error_count: 2
      }

      summary = Reporter.format_summary(report, false)

      assert summary =~ "2 errors"
    end

    test "formats summary with errors and warnings" do
      report = %{
        Reporter.new("test.phr")
        | error_count: 3,
          warning_count: 5
      }

      summary = Reporter.format_summary(report, false)

      assert summary =~ "3 errors"
      assert summary =~ "5 warnings"
    end

    test "uses singular form for single error" do
      report = %{
        Reporter.new("test.phr")
        | error_count: 1
      }

      summary = Reporter.format_summary(report, false)

      assert summary =~ "1 error"
      refute summary =~ "errors"
    end
  end

  describe "Reporter.to_json/1" do
    test "exports report to JSON" do
      report = Reporter.new("test.phr")
      location = %{file: "test.phr", line: 10, column: 5}

      diagnostic =
        Diagnostics.new("E0001", :error, "test error", location,
          suggestion: "fix it",
          help: "help text"
        )

      updated = Reporter.add(report, diagnostic)
      json = Reporter.to_json(updated)

      assert json =~ "\"file\": \"test.phr\""
      assert json =~ "\"code\": \"E0001\""
      assert json =~ "\"severity\": \"error\""
      assert json =~ "\"message\": \"test error\""
      assert json =~ "\"line\": 10"
      assert json =~ "\"column\": 5"
      assert json =~ "\"suggestion\": \"fix it\""
      assert json =~ "\"help\": \"help text\""
    end
  end

  describe "Suggestions.levenshtein_distance/2" do
    test "calculates distance for identical strings" do
      assert Suggestions.levenshtein_distance("hello", "hello") == 0
    end

    test "calculates distance for single substitution" do
      assert Suggestions.levenshtein_distance("hello", "hallo") == 1
    end

    test "calculates distance for single insertion" do
      assert Suggestions.levenshtein_distance("hello", "helloo") == 1
    end

    test "calculates distance for single deletion" do
      assert Suggestions.levenshtein_distance("hello", "helo") == 1
    end

    test "calculates distance for multiple edits" do
      assert Suggestions.levenshtein_distance("kitten", "sitting") == 3
    end

    test "is case insensitive" do
      assert Suggestions.levenshtein_distance("HELLO", "hello") == 0
      assert Suggestions.levenshtein_distance("Hello", "HELLO") == 0
    end
  end

  describe "Suggestions.find_similar/3" do
    test "finds the most similar name" do
      available = ["risk_level", "max_value", "threshold"]
      similar = Suggestions.find_similar("risk_levle", available)

      assert similar == "risk_level"
    end

    test "returns nil when no good match" do
      available = ["foo", "bar", "baz"]
      similar = Suggestions.find_similar("completely_different", available)

      assert similar == nil
    end

    test "respects threshold parameter" do
      available = ["risk_level", "max_value"]
      similar = Suggestions.find_similar("risk_levle", available, threshold: 0)

      assert similar == nil
    end

    test "finds closest match among multiple candidates" do
      available = ["risk_level", "max_value", "threshold"]
      similar = Suggestions.find_similar("risk_levl", available)

      # Should find risk_level (distance 1) not max_value (distance >3)
      assert similar == "risk_level"
    end
  end

  describe "Suggestions.find_similar_constant/3" do
    test "finds similar constant names in AST" do
      ast = [
        {:const, :max_value, 100},
        {:const, :threshold, 0.75}
      ]

      similar = Suggestions.find_similar_constant("max_valu", ast)

      assert similar == "max_value"
    end

    test "returns nil when no constants" do
      ast = []
      similar = Suggestions.find_similar_constant("max_value", ast)

      assert similar == nil
    end
  end

  describe "Suggestions.find_similar_policy/3" do
    test "finds similar policy names in AST" do
      ast = [
        {:policy, :security_check, {:var, :risk}, {:accept}, %{}},
        {:policy, :validation, {:var, :valid}, {:reject}, %{}}
      ]

      similar = Suggestions.find_similar_policy("security_chek", ast)

      assert similar == "security_check"
    end
  end

  describe "integration test" do
    test "complete diagnostic workflow" do
      # Create a report
      report = Reporter.new("example.phr")

      # Add various diagnostics
      location1 = %{file: "example.phr", line: 5, column: 10}
      error = Diagnostics.undefined_variable("risk_levle", "example.phr", 5, 10)

      location2 = %{file: "example.phr", line: 8, column: 3}
      warning = Diagnostics.unused_import("Std.Temporal", "example.phr", 8, 3)

      report =
        report
        |> Reporter.add(error)
        |> Reporter.add(warning)

      # Check counts
      assert report.error_count == 1
      assert report.warning_count == 1

      # Format the report
      formatted = Reporter.format(report, color: false)
      assert formatted =~ "error[E0042]"
      assert formatted =~ "warning[W0400]"
      assert formatted =~ "1 error, 1 warning"

      # Export to JSON
      json = Reporter.to_json(report)
      assert json =~ "\"errors\": 1"
      assert json =~ "\"warnings\": 1"
    end
  end
end
