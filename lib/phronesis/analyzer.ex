# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Analyzer do
  @moduledoc """
  Static analysis for Phronesis policy files.

  Performs deep analysis beyond syntax checking:
  - Dead code detection
  - Unreachable policy branches
  - Unused imports and constants
  - Constant propagation analysis
  - Consensus threshold validation
  - Security vulnerability scanning

  ## Usage

      # Analyze a single file
      {:ok, issues} = Analyzer.analyze_file("policy.phr")

      # Analyze with options
      {:ok, issues} = Analyzer.analyze_file("policy.phr",
        severity: :warning,
        checks: [:dead_code, :unused_imports]
      )

      # Analyze entire project
      {:ok, results} = Analyzer.analyze_project("./policies")
  """

  alias Phronesis.{Lexer, Parser}

  @type severity :: :error | :warning | :info
  @type issue :: %{
          severity: severity(),
          check: atom(),
          message: String.t(),
          file: String.t(),
          line: integer(),
          column: integer() | nil,
          suggestion: String.t() | nil
        }

  @type analysis_result :: %{
          file: String.t(),
          issues: [issue()],
          stats: %{
            errors: integer(),
            warnings: integer(),
            info: integer()
          }
        }

  ## Public API

  @doc """
  Analyze a single file for issues.
  """
  def analyze_file(file_path, opts \\ []) do
    with {:ok, source} <- File.read(file_path),
         {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      issues = run_checks(ast, source, file_path, opts)
      result = build_result(file_path, issues)
      {:ok, result}
    else
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Analyze an entire project directory.
  """
  def analyze_project(directory, opts \\ []) do
    files =
      Path.wildcard(Path.join(directory, "**/*.phr"))
      |> Enum.sort()

    results =
      Enum.map(files, fn file ->
        case analyze_file(file, opts) do
          {:ok, result} -> result
          {:error, _} -> nil
        end
      end)
      |> Enum.reject(&is_nil/1)

    {:ok, results}
  end

  ## Analysis Checks

  defp run_checks(ast, source, file_path, opts) do
    enabled_checks = Keyword.get(opts, :checks, :all)
    min_severity = Keyword.get(opts, :severity, :info)

    all_issues =
      []
      |> maybe_add_check(enabled_checks, :dead_code, fn -> check_dead_code(ast, file_path) end)
      |> maybe_add_check(enabled_checks, :unreachable, fn -> check_unreachable_policies(ast, file_path) end)
      |> maybe_add_check(enabled_checks, :unused_imports, fn -> check_unused_imports(ast, file_path) end)
      |> maybe_add_check(enabled_checks, :unused_constants, fn -> check_unused_constants(ast, file_path) end)
      |> maybe_add_check(enabled_checks, :constant_propagation, fn -> check_constant_values(ast, file_path) end)
      |> maybe_add_check(enabled_checks, :consensus_threshold, fn ->
        check_consensus_thresholds(ast, file_path)
      end)
      |> maybe_add_check(enabled_checks, :security, fn -> check_security_issues(ast, source, file_path) end)

    # Filter by severity
    Enum.filter(all_issues, fn issue ->
      severity_level(issue.severity) >= severity_level(min_severity)
    end)
  end

  defp maybe_add_check(issues, :all, _check_name, check_fn) do
    issues ++ check_fn.()
  end

  defp maybe_add_check(issues, enabled_checks, check_name, check_fn) do
    if check_name in enabled_checks do
      issues ++ check_fn.()
    else
      issues
    end
  end

  defp severity_level(:error), do: 3
  defp severity_level(:warning), do: 2
  defp severity_level(:info), do: 1

  ## Check: Dead Code Detection

  defp check_dead_code(ast, file_path) do
    # Check for policies with 'false' conditions
    ast
    |> Enum.filter(&match?({:policy, _, _, _, _}, &1))
    |> Enum.reduce([], fn {:policy, name, condition, _action, meta}, issues ->
      if always_false?(condition) do
        [
          %{
            severity: :warning,
            check: :dead_code,
            message: "Policy '#{name}' has a condition that is always false",
            file: file_path,
            line: meta[:line] || 0,
            column: nil,
            suggestion: "Remove this policy or fix the condition"
          }
          | issues
        ]
      else
        issues
      end
    end)
  end

  defp always_false?({:literal, :boolean, false}), do: true
  defp always_false?({:and, left, right}), do: always_false?(left) or always_false?(right)
  defp always_false?(_), do: false

  ## Check: Unreachable Policy Branches

  defp check_unreachable_policies(ast, file_path) do
    policies =
      ast
      |> Enum.filter(&match?({:policy, _, _, _, _}, &1))
      |> Enum.sort_by(fn {:policy, _, _, _, meta} -> -meta[:priority] end)

    check_policy_reachability(policies, file_path, [])
  end

  defp check_policy_reachability([], _file_path, acc), do: acc

  defp check_policy_reachability([{:policy, name, condition, _action, meta} | rest], file_path, acc) do
    # Check if this policy can never match due to earlier policies
    if always_true?(condition) do
      # All subsequent policies are unreachable
      unreachable_issues =
        Enum.map(rest, fn {:policy, unreachable_name, _, _, unreachable_meta} ->
          %{
            severity: :warning,
            check: :unreachable,
            message:
              "Policy '#{unreachable_name}' is unreachable because '#{name}' always matches and has higher priority",
            file: file_path,
            line: unreachable_meta[:line] || 0,
            column: nil,
            suggestion: "Remove this policy or adjust priorities"
          }
        end)

      acc ++ unreachable_issues
    else
      check_policy_reachability(rest, file_path, acc)
    end
  end

  defp always_true?({:literal, :boolean, true}), do: true
  defp always_true?({:or, left, right}), do: always_true?(left) and always_true?(right)
  defp always_true?(_), do: false

  ## Check: Unused Imports

  defp check_unused_imports(ast, file_path) do
    imports = extract_imports(ast)
    usages = extract_module_usages(ast)

    unused =
      Enum.reject(imports, fn {module_path, _meta} ->
        module_name = List.last(module_path)
        module_name in usages or Enum.join(module_path, ".") in usages
      end)

    Enum.map(unused, fn {module_path, meta} ->
      %{
        severity: :warning,
        check: :unused_imports,
        message: "Unused import: #{Enum.join(module_path, ".")}",
        file: file_path,
        line: meta[:line] || 0,
        column: nil,
        suggestion: "Remove this import if not needed"
      }
    end)
  end

  defp extract_imports(ast) do
    ast
    |> Enum.filter(&match?({:import, _, _}, &1))
    |> Enum.map(fn {:import, path, meta} -> {path, meta} end)
  end

  defp extract_module_usages(ast) do
    ast
    |> Enum.flat_map(&extract_usages_from_node/1)
    |> Enum.uniq()
  end

  defp extract_usages_from_node({:policy, _name, condition, action, _meta}) do
    extract_usages_from_expr(condition) ++ extract_usages_from_expr(action)
  end

  defp extract_usages_from_node(_), do: []

  defp extract_usages_from_expr({:call, {:module_access, module, _function}, _args}) do
    [module]
  end

  defp extract_usages_from_expr({:module_access, module, _field}) do
    [module]
  end

  defp extract_usages_from_expr({op, left, right})
       when op in [:and, :or, :comparison, :add, :subtract, :multiply, :divide] do
    extract_usages_from_expr(left) ++ extract_usages_from_expr(right)
  end

  defp extract_usages_from_expr({:not, expr}), do: extract_usages_from_expr(expr)
  defp extract_usages_from_expr(_), do: []

  ## Check: Unused Constants

  defp check_unused_constants(ast, file_path) do
    constants = extract_constants_map(ast)
    usages = extract_constant_usages(ast)

    unused =
      Enum.reject(constants, fn {name, _meta} ->
        name in usages
      end)

    Enum.map(unused, fn {name, meta} ->
      %{
        severity: :info,
        check: :unused_constants,
        message: "Unused constant: #{name}",
        file: file_path,
        line: meta[:line] || 0,
        column: nil,
        suggestion: "Remove this constant if not needed"
      }
    end)
  end

  defp extract_constants_map(ast) do
    ast
    |> Enum.filter(&match?({:const, _, _}, &1))
    |> Enum.map(fn {:const, name, _value} -> {to_string(name), %{}} end)
  end

  defp extract_constant_usages(ast) do
    ast
    |> Enum.flat_map(&extract_const_usages_from_node/1)
    |> Enum.uniq()
  end

  defp extract_const_usages_from_node({:policy, _name, condition, action, _meta}) do
    extract_identifiers(condition) ++ extract_identifiers(action)
  end

  defp extract_const_usages_from_node(_), do: []

  defp extract_identifiers({:identifier, name}), do: [name]

  defp extract_identifiers({op, left, right})
       when op in [:and, :or, :comparison, :add, :subtract, :multiply, :divide, :lt, :gt, :eq, :neq, :lte, :gte] do
    extract_identifiers(left) ++ extract_identifiers(right)
  end

  defp extract_identifiers({:not, expr}), do: extract_identifiers(expr)
  defp extract_identifiers({:call, _fn, args}) when is_list(args), do: Enum.flat_map(args, &extract_identifiers/1)
  defp extract_identifiers(_), do: []

  ## Check: Constant Values

  defp check_constant_values(ast, file_path) do
    ast
    |> Enum.filter(&match?({:const, _, _}, &1))
    |> Enum.reduce([], fn {:const, name, value}, issues ->
      case validate_constant_value(name, value) do
        :ok ->
          issues

        {:warning, message, suggestion} ->
          [
            %{
              severity: :warning,
              check: :constant_propagation,
              message: message,
              file: file_path,
              line: 0,
              column: nil,
              suggestion: suggestion
            }
            | issues
          ]
      end
    end)
  end

  defp validate_constant_value(_name, {:literal, :integer, value}) when value < 0 do
    {:warning, "Negative constant value may indicate an error", "Verify this value is correct"}
  end

  defp validate_constant_value(_name, _value), do: :ok

  ## Check: Consensus Thresholds

  defp check_consensus_thresholds(ast, file_path) do
    ast
    |> Enum.filter(&match?({:const, _, _}, &1))
    |> Enum.reduce([], fn {:const, name, value}, issues ->
      name_str = to_string(name)

      if String.contains?(name_str, "threshold") or String.contains?(name_str, "quorum") do
        case extract_numeric_value(value) do
          nil ->
            issues

          numeric when is_float(numeric) and (numeric < 0.0 or numeric > 1.0) ->
            [
              %{
                severity: :error,
                check: :consensus_threshold,
                message: "Consensus threshold '#{name}' must be between 0.0 and 1.0, got #{numeric}",
                file: file_path,
                line: 0,
                column: nil,
                suggestion: "Use a value between 0.0 (0%) and 1.0 (100%)"
              }
              | issues
            ]

          _ ->
            issues
        end
      else
        issues
      end
    end)
  end

  defp extract_numeric_value({:literal, :float, value}), do: value
  defp extract_numeric_value({:literal, :integer, value}), do: value * 1.0
  defp extract_numeric_value(_), do: nil

  ## Check: Security Issues

  defp check_security_issues(ast, source, file_path) do
    []
    |> check_hardcoded_secrets(source, file_path)
    |> check_unrestricted_policies(ast, file_path)
    |> check_dangerous_patterns(ast, file_path)
  end

  defp check_hardcoded_secrets(acc, source, file_path) do
    # Check for common secret patterns
    secret_patterns = [
      ~r/password\s*=\s*["'][^"']+["']/i,
      ~r/api[_-]?key\s*=\s*["'][^"']+["']/i,
      ~r/secret\s*=\s*["'][^"']+["']/i,
      ~r/token\s*=\s*["'][^"']+["']/i
    ]

    lines = String.split(source, "\n")

    Enum.reduce(secret_patterns, acc, fn pattern, issues ->
      matching_lines =
        lines
        |> Enum.with_index(1)
        |> Enum.filter(fn {line, _} -> Regex.match?(pattern, line) end)

      new_issues =
        Enum.map(matching_lines, fn {_line, line_num} ->
          %{
            severity: :error,
            check: :security,
            message: "Possible hardcoded secret detected",
            file: file_path,
            line: line_num,
            column: nil,
            suggestion: "Use environment variables or configuration files for secrets"
          }
        end)

      issues ++ new_issues
    end)
  end

  defp check_unrestricted_policies(acc, ast, file_path) do
    ast
    |> Enum.filter(&match?({:policy, _, _, _, _}, &1))
    |> Enum.reduce(acc, fn {:policy, name, condition, action, meta}, issues ->
      if overly_permissive?(condition, action) do
        [
          %{
            severity: :warning,
            check: :security,
            message: "Policy '#{name}' may be overly permissive",
            file: file_path,
            line: meta[:line] || 0,
            column: nil,
            suggestion: "Add more specific conditions to restrict this policy"
          }
          | issues
        ]
      else
        issues
      end
    end)
  end

  defp overly_permissive?({:literal, :boolean, true}, {:accept, _}), do: true
  defp overly_permissive?(_, _), do: false

  defp check_dangerous_patterns(acc, ast, file_path) do
    # Check for policies with very low priority that always accept
    ast
    |> Enum.filter(&match?({:policy, _, _, _, _}, &1))
    |> Enum.reduce(acc, fn {:policy, name, _condition, action, meta}, issues ->
      priority = meta[:priority] || 0

      if priority < 10 and match?({:accept, _}, action) do
        [
          %{
            severity: :info,
            check: :security,
            message: "Policy '#{name}' has very low priority and accepts - may be a catch-all",
            file: file_path,
            line: meta[:line] || 0,
            column: nil,
            suggestion: "Verify this is intentional for a default accept policy"
          }
          | issues
        ]
      else
        issues
      end
    end)
  end

  ## Result Building

  defp build_result(file_path, issues) do
    stats = %{
      errors: Enum.count(issues, &(&1.severity == :error)),
      warnings: Enum.count(issues, &(&1.severity == :warning)),
      info: Enum.count(issues, &(&1.severity == :info))
    }

    %{
      file: file_path,
      issues: Enum.sort_by(issues, & &1.line),
      stats: stats
    }
  end

  ## Formatting

  @doc """
  Format analysis results for display.
  """
  def format_results(results) when is_list(results) do
    total_stats = %{errors: 0, warnings: 0, info: 0}

    {output, final_stats} =
      Enum.reduce(results, {"", total_stats}, fn result, {acc, stats} ->
        file_output = format_file_result(result)

        new_stats = %{
          errors: stats.errors + result.stats.errors,
          warnings: stats.warnings + result.stats.warnings,
          info: stats.info + result.stats.info
        }

        {acc <> file_output, new_stats}
      end)

    summary = format_summary(final_stats, length(results))
    output <> "\n" <> summary
  end

  def format_results(result) when is_map(result) do
    file_output = format_file_result(result)
    summary = format_summary(result.stats, 1)
    file_output <> "\n" <> summary
  end

  defp format_file_result(%{file: file, issues: issues}) do
    if Enum.empty?(issues) do
      "✓ #{Path.basename(file)} - No issues found\n"
    else
      header = "\n#{Path.basename(file)}:\n"

      issues_text =
        Enum.map_join(issues, "\n", fn issue ->
          severity_icon = severity_icon(issue.severity)
          location = "  #{issue.line}:#{issue.column || 0}"

          message = "#{severity_icon} #{location} #{issue.message}"

          if issue.suggestion do
            message <> "\n      → #{issue.suggestion}"
          else
            message
          end
        end)

      header <> issues_text <> "\n"
    end
  end

  defp format_summary(stats, file_count) do
    """

    Analysis Summary (#{file_count} file#{if file_count != 1, do: "s", else: ""}):
      #{stats.errors} error(s)
      #{stats.warnings} warning(s)
      #{stats.info} info message(s)
    """
  end

  defp severity_icon(:error), do: "✗"
  defp severity_icon(:warning), do: "⚠"
  defp severity_icon(:info), do: "ℹ"
end
