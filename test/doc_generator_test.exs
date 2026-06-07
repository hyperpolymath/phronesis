# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule Phronesis.DocGeneratorTest do
  use ExUnit.Case, async: true
  alias Phronesis.DocGenerator

  @test_policy_path "examples/documented_policy.phr"

  describe "generate_file/1" do
    test "extracts documentation from policy file" do
      assert {:ok, docs} = DocGenerator.generate_file(@test_policy_path)

      # Check project metadata
      assert docs.project_name == "documented_policy"

      # Check constants extracted
      assert length(docs.constants) == 2
      threshold_const = Enum.find(docs.constants, &(&1.name == "threshold"))
      assert threshold_const != nil
      assert threshold_const.description =~ "risk threshold"

      # Check policies extracted
      assert length(docs.policies) >= 3
      security_policy = Enum.find(docs.policies, &(&1.name == "security_check"))
      assert security_policy != nil
      assert security_policy.description =~ "Primary security validation"
    end

    test "handles files without documentation" do
      # Use a basic example file
      assert {:ok, docs} = DocGenerator.generate_file("examples/sample.phr")
      assert docs.constants != []
      assert docs.policies != []
    end

    test "returns error for non-existent file" do
      assert {:error, _} = DocGenerator.generate_file("nonexistent.phr")
    end

    test "returns error for unparseable file" do
      # Create a temporary invalid file
      temp_file = "/tmp/invalid_#{System.unique_integer()}.phr"
      File.write!(temp_file, "INVALID SYNTAX !!!")

      assert {:error, _} = DocGenerator.generate_file(temp_file)

      File.rm!(temp_file)
    end
  end

  describe "generate_project/2" do
    test "generates documentation for examples directory" do
      assert {:ok, docs} = DocGenerator.generate_project("examples", name: "Phronesis Examples")

      # Should include multiple files
      assert length(docs.files) > 0

      # Should have aggregated constants and policies
      assert length(docs.constants) > 0
      assert length(docs.policies) > 0

      # Should have project name
      assert docs.project_name == "Phronesis Examples"
    end

    test "handles empty directory" do
      # Create temporary empty directory
      temp_dir = "/tmp/empty_#{System.unique_integer()}"
      File.mkdir_p!(temp_dir)

      assert {:ok, docs} = DocGenerator.generate_project(temp_dir)
      assert docs.files == []

      File.rm_rf!(temp_dir)
    end

    test "returns error for non-existent directory" do
      assert {:error, _} = DocGenerator.generate_project("nonexistent_directory")
    end
  end

  describe "export_html/2" do
    test "generates HTML documentation files" do
      {:ok, docs} = DocGenerator.generate_file(@test_policy_path)

      output_dir = "/tmp/docs_html_#{System.unique_integer()}"
      assert {:ok, ^output_dir} = DocGenerator.export_html(docs, output_dir)

      # Check that files were created
      assert File.exists?(Path.join(output_dir, "index.html"))
      assert File.exists?(Path.join(output_dir, "styles.css"))

      # Check index.html contains expected content
      index_content = File.read!(Path.join(output_dir, "index.html"))
      assert index_content =~ "documented_policy"
      assert index_content =~ "threshold"
      assert index_content =~ "security_check"

      # Cleanup
      File.rm_rf!(output_dir)
    end

    test "creates output directory if it doesn't exist" do
      {:ok, docs} = DocGenerator.generate_file(@test_policy_path)

      output_dir = "/tmp/docs_new_#{System.unique_integer()}"
      assert {:ok, ^output_dir} = DocGenerator.export_html(docs, output_dir)
      assert File.dir?(output_dir)

      File.rm_rf!(output_dir)
    end
  end

  describe "export_markdown/2" do
    test "generates Markdown documentation files" do
      {:ok, docs} = DocGenerator.generate_file(@test_policy_path)

      output_dir = "/tmp/docs_md_#{System.unique_integer()}"
      assert {:ok, ^output_dir} = DocGenerator.export_markdown(docs, output_dir)

      # Check that files were created
      assert File.exists?(Path.join(output_dir, "README.md"))
      assert File.exists?(Path.join(output_dir, "CONSTANTS.md"))
      assert File.exists?(Path.join(output_dir, "POLICIES.md"))

      # Check README.md contains expected content
      readme = File.read!(Path.join(output_dir, "README.md"))
      assert readme =~ "documented_policy"

      # Check CONSTANTS.md
      constants_md = File.read!(Path.join(output_dir, "CONSTANTS.md"))
      assert constants_md =~ "threshold"

      # Check POLICIES.md
      policies_md = File.read!(Path.join(output_dir, "POLICIES.md"))
      assert policies_md =~ "security_check"

      # Cleanup
      File.rm_rf!(output_dir)
    end

    test "creates output directory if it doesn't exist" do
      {:ok, docs} = DocGenerator.generate_file(@test_policy_path)

      output_dir = "/tmp/docs_md_new_#{System.unique_integer()}"
      assert {:ok, ^output_dir} = DocGenerator.export_markdown(docs, output_dir)
      assert File.dir?(output_dir)

      File.rm_rf!(output_dir)
    end
  end

  describe "comment extraction" do
    test "extracts multi-line documentation comments" do
      {:ok, docs} = DocGenerator.generate_file(@test_policy_path)

      # Find the security_check policy
      security_policy = Enum.find(docs.policies, &(&1.name == "security_check"))
      assert security_policy != nil

      # Should have extracted the full description
      assert security_policy.description =~ "Primary security validation"
      assert security_policy.description =~ "risk level exceeds"
    end

    test "extracts examples from comments" do
      {:ok, docs} = DocGenerator.generate_file(@test_policy_path)

      # Find the threshold constant
      threshold_const = Enum.find(docs.constants, &(&1.name == "threshold"))
      assert threshold_const != nil

      # Should have extracted example
      assert length(threshold_const.examples) > 0
      example = hd(threshold_const.examples)
      assert example =~ "CONST threshold = 75"
    end
  end

  describe "project documentation" do
    test "aggregates documentation from multiple files" do
      {:ok, docs} = DocGenerator.generate_project("examples")

      # Should have documentation from multiple example files
      assert length(docs.files) >= 2

      # Should aggregate all constants
      all_constants = Enum.map(docs.constants, & &1.name)
      assert "threshold" in all_constants

      # Should aggregate all policies
      all_policies = Enum.map(docs.policies, & &1.name)
      assert length(all_policies) > 0
    end

    test "builds cross-reference index" do
      {:ok, docs} = DocGenerator.generate_project("examples")

      # Index should contain references to constants and policies
      assert is_map(docs.index)
    end
  end
end
