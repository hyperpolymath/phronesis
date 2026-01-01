# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.ConformanceTest do
  @moduledoc """
  Conformance test suite for Phronesis.

  Per the semantic anchor:
  - "Conformance corpus: 5 valid + 5 invalid rule sets"
  - "invalid rules fail deterministically"
  """

  use ExUnit.Case, async: true

  @valid_dir Path.join([File.cwd!(), "priv", "conformance", "valid"])
  @invalid_dir Path.join([File.cwd!(), "priv", "conformance", "invalid"])

  describe "valid conformance tests" do
    test "01_simple_policy.phr parses successfully" do
      assert_valid_policy("01_simple_policy.phr")
    end

    test "02_constants_and_policy.phr parses successfully" do
      assert_valid_policy("02_constants_and_policy.phr")
    end

    test "03_multiple_policies.phr parses successfully" do
      assert_valid_policy("03_multiple_policies.phr")
    end

    test "04_boolean_logic.phr parses successfully" do
      assert_valid_policy("04_boolean_logic.phr")
    end

    test "05_arithmetic_and_comparison.phr parses successfully" do
      assert_valid_policy("05_arithmetic_and_comparison.phr")
    end
  end

  describe "invalid conformance tests" do
    test "01_missing_then.phr fails to parse" do
      assert_invalid_policy("01_missing_then.phr")
    end

    test "02_missing_priority.phr fails to parse" do
      assert_invalid_policy("02_missing_priority.phr")
    end

    test "03_invalid_operator.phr fails to parse" do
      assert_invalid_policy("03_invalid_operator.phr")
    end

    test "04_unclosed_string.phr fails to parse" do
      assert_invalid_policy("04_unclosed_string.phr")
    end

    test "05_reserved_word_identifier.phr fails to parse" do
      assert_invalid_policy("05_reserved_word_identifier.phr")
    end
  end

  describe "conformance corpus completeness" do
    test "valid directory contains 5 test files" do
      {:ok, files} = File.ls(@valid_dir)
      phr_files = Enum.filter(files, &String.ends_with?(&1, ".phr"))
      assert length(phr_files) >= 5, "Expected at least 5 valid conformance tests"
    end

    test "invalid directory contains 5 test files" do
      {:ok, files} = File.ls(@invalid_dir)
      phr_files = Enum.filter(files, &String.ends_with?(&1, ".phr"))
      assert length(phr_files) >= 5, "Expected at least 5 invalid conformance tests"
    end
  end

  # Helper functions

  defp assert_valid_policy(filename) do
    path = Path.join(@valid_dir, filename)
    assert File.exists?(path), "Test file not found: #{path}"

    {:ok, source} = File.read(path)
    result = Phronesis.parse(source)

    assert {:ok, ast} = result, "Expected #{filename} to parse successfully, got: #{inspect(result)}"
    assert is_list(ast), "Expected AST to be a list"
  end

  defp assert_invalid_policy(filename) do
    path = Path.join(@invalid_dir, filename)
    assert File.exists?(path), "Test file not found: #{path}"

    {:ok, source} = File.read(path)
    result = Phronesis.parse(source)

    assert {:error, _reason} = result,
           "Expected #{filename} to fail parsing, but it succeeded with: #{inspect(result)}"
  end
end
