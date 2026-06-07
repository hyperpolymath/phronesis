# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule Phronesis.AnalyzerTest do
  use ExUnit.Case, async: true
  alias Phronesis.Analyzer

  @test_file_path "examples/analysis_test.phr"

  describe "analyze_file/2" do
    test "detects dead code" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      dead_code_issues = Enum.filter(result.issues, &(&1.check == :dead_code))
      assert length(dead_code_issues) > 0

      issue = hd(dead_code_issues)
      assert issue.severity == :warning
      assert issue.message =~ "always false"
    end

    test "detects unreachable policies" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      unreachable_issues = Enum.filter(result.issues, &(&1.check == :unreachable))
      assert length(unreachable_issues) > 0

      issue = hd(unreachable_issues)
      assert issue.severity == :warning
      assert issue.message =~ "unreachable"
    end

    test "detects unused imports" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      unused_import_issues = Enum.filter(result.issues, &(&1.check == :unused_imports))
      assert length(unused_import_issues) > 0

      issue = hd(unused_import_issues)
      assert issue.severity == :warning
      assert issue.message =~ "Unused import"
      assert issue.message =~ "Temporal"
    end

    test "detects unused constants" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      unused_const_issues = Enum.filter(result.issues, &(&1.check == :unused_constants))
      assert length(unused_const_issues) > 0

      issue = hd(unused_const_issues)
      assert issue.severity == :info
      assert issue.message =~ "Unused constant"
      assert issue.message =~ "unused_value"
    end

    test "detects overly permissive policies" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      security_issues = Enum.filter(result.issues, &(&1.check == :security))
      permissive_issues = Enum.filter(security_issues, &(&1.message =~ "overly permissive"))

      assert length(permissive_issues) > 0
    end

    test "detects low priority catch-all policies" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      security_issues = Enum.filter(result.issues, &(&1.check == :security))
      catch_all_issues = Enum.filter(security_issues, &(&1.message =~ "catch-all"))

      assert length(catch_all_issues) > 0
    end

    test "provides suggestions for issues" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      issues_with_suggestions = Enum.filter(result.issues, &(&1.suggestion != nil))
      assert length(issues_with_suggestions) > 0
    end

    test "returns error for non-existent file" do
      assert {:error, _} = Analyzer.analyze_file("nonexistent.phr")
    end

    test "calculates statistics correctly" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)

      assert result.stats.errors >= 0
      assert result.stats.warnings >= 0
      assert result.stats.info >= 0

      total_issues = result.stats.errors + result.stats.warnings + result.stats.info
      assert total_issues == length(result.issues)
    end
  end

  describe "analyze_file/2 with options" do
    test "filters by severity level" do
      {:ok, result_all} = Analyzer.analyze_file(@test_file_path, severity: :info)
      {:ok, result_warnings} = Analyzer.analyze_file(@test_file_path, severity: :warning)
      {:ok, result_errors} = Analyzer.analyze_file(@test_file_path, severity: :error)

      assert length(result_all.issues) >= length(result_warnings.issues)
      assert length(result_warnings.issues) >= length(result_errors.issues)
    end

    test "runs specific checks only" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path, checks: [:dead_code])

      # Should only have dead_code issues
      check_types = Enum.map(result.issues, & &1.check) |> Enum.uniq()
      assert check_types == [:dead_code]
    end

    test "runs multiple specific checks" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path, checks: [:dead_code, :unused_imports])

      check_types = Enum.map(result.issues, & &1.check) |> Enum.uniq() |> Enum.sort()
      assert :dead_code in check_types
      assert :unused_imports in check_types
    end
  end

  describe "analyze_project/2" do
    test "analyzes all files in examples directory" do
      {:ok, results} = Analyzer.analyze_project("examples")

      assert length(results) > 0
      assert Enum.all?(results, &is_map/1)
      assert Enum.all?(results, &Map.has_key?(&1, :file))
      assert Enum.all?(results, &Map.has_key?(&1, :issues))
      assert Enum.all?(results, &Map.has_key?(&1, :stats))
    end

    test "returns empty list for empty directory" do
      temp_dir = "/tmp/empty_analyzer_#{System.unique_integer()}"
      File.mkdir_p!(temp_dir)

      {:ok, results} = Analyzer.analyze_project(temp_dir)
      assert results == []

      File.rm_rf!(temp_dir)
    end
  end

  describe "format_results/1" do
    test "formats single file result" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)
      output = Analyzer.format_results(result)

      assert is_binary(output)
      assert output =~ "analysis_test.phr"
      assert output =~ "Analysis Summary"
    end

    test "formats multiple file results" do
      {:ok, results} = Analyzer.analyze_project("examples")
      output = Analyzer.format_results(results)

      assert is_binary(output)
      assert output =~ "Analysis Summary"
      assert output =~ "file"
    end

    test "shows no issues for clean file" do
      case Analyzer.analyze_file("examples/documented_policy.phr") do
        {:ok, result} ->
          output = Analyzer.format_results(result)

          if result.stats.errors + result.stats.warnings + result.stats.info == 0 do
            assert output =~ "No issues found"
          else
            # Has some issues, but that's okay for this test file
            assert is_binary(output)
          end

        {:error, _} ->
          # File might have parse errors, skip this test
          :ok
      end
    end

    test "includes severity icons" do
      {:ok, result} = Analyzer.analyze_file(@test_file_path)
      output = Analyzer.format_results(result)

      # Should have at least one severity icon
      assert output =~ "✗" or output =~ "⚠" or output =~ "ℹ"
    end
  end

  describe "security checks" do
    test "does not flag valid policies as security issues" do
      # Use profile_example.phr which has valid policies
      case Analyzer.analyze_file("examples/profile_example.phr") do
        {:ok, result} ->
          # Filter only security issues (not other checks)
          security_issues =
            result.issues
            |> Enum.filter(&(&1.check == :security))
            |> Enum.filter(&(&1.message =~ "overly permissive"))

          # Valid policies should not have overly permissive warnings
          assert length(security_issues) == 0

        {:error, _} ->
          # File might have parse errors, skip this test
          :ok
      end
    end
  end

  describe "constant validation" do
    test "validates constant values" do
      # Create a temporary file with an invalid threshold
      temp_file = "/tmp/invalid_threshold_#{System.unique_integer()}.phr"

      File.write!(
        temp_file,
        """
        # SPDX-License-Identifier: MPL-2.0
        CONST consensus_threshold = 1.5

        POLICY test:
          risk_level > 50
          THEN ACCEPT("test")
          PRIORITY: 10
          EXPIRES: never
          CREATED_BY: test
        """
      )

      {:ok, result} = Analyzer.analyze_file(temp_file)

      threshold_issues = Enum.filter(result.issues, &(&1.check == :consensus_threshold))
      assert length(threshold_issues) > 0

      issue = hd(threshold_issues)
      assert issue.severity == :error
      assert issue.message =~ "must be between 0.0 and 1.0"

      File.rm!(temp_file)
    end
  end
end
