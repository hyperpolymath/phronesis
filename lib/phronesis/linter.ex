# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Linter do
  @moduledoc """
  Static analysis linter for Phronesis policy language.

  Performs static analysis to detect:
  - Style issues
  - Potential bugs
  - Security concerns
  - Performance issues
  - Best practice violations
  """

  alias Phronesis.{Lexer, Parser}

  @type severity :: :error | :warning | :info
  @type issue :: %{
    severity: severity(),
    code: String.t(),
    message: String.t(),
    line: pos_integer(),
    column: pos_integer(),
    suggestion: String.t() | nil
  }

  @doc """
  Lint source code.

  Returns a list of issues found.
  """
  @spec lint(String.t(), keyword()) :: {:ok, [issue()]} | {:error, term()}
  def lint(source, opts \\ []) do
    enabled_rules = Keyword.get(opts, :rules, default_rules())

    with {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      issues =
        enabled_rules
        |> Enum.flat_map(fn rule -> apply_rule(rule, source, tokens, ast) end)
        |> Enum.sort_by(fn issue -> {issue.line, issue.column} end)

      {:ok, issues}
    end
  end

  @doc """
  Lint a file.
  """
  @spec lint_file(Path.t(), keyword()) :: {:ok, [issue()]} | {:error, term()}
  def lint_file(path, opts \\ []) do
    with {:ok, source} <- File.read(path) do
      lint(source, opts)
    end
  end

  @doc """
  Format issues for terminal output.
  """
  @spec format_issues([issue()], String.t()) :: String.t()
  def format_issues(issues, filename \\ "<stdin>") do
    if issues == [] do
      "No issues found."
    else
      issues
      |> Enum.map(fn issue ->
        severity_str = format_severity(issue.severity)
        suggestion = if issue.suggestion, do: "\n  Suggestion: #{issue.suggestion}", else: ""
        "#{filename}:#{issue.line}:#{issue.column}: #{severity_str} [#{issue.code}] #{issue.message}#{suggestion}"
      end)
      |> Enum.join("\n")
    end
  end

  # ============================================================
  # Rules Configuration
  # ============================================================

  defp default_rules do
    [
      :unused_const,
      :shadowed_binding,
      :empty_policy,
      :unreachable_policy,
      :hardcoded_credentials,
      :overly_permissive,
      :missing_priority,
      :duplicate_policy_name,
      :long_line,
      :trailing_whitespace,
      :mixed_indentation,
      :undefined_identifier,
      :deprecated_syntax
    ]
  end

  # ============================================================
  # Rule Implementations
  # ============================================================

  defp apply_rule(:unused_const, _source, _tokens, ast) do
    {defined, used} = collect_const_usage(ast)
    unused = MapSet.difference(defined, used)

    unused
    |> MapSet.to_list()
    |> Enum.map(fn {name, line, col} ->
      %{
        severity: :warning,
        code: "W001",
        message: "Constant '#{name}' is defined but never used",
        line: line,
        column: col,
        suggestion: "Remove the unused constant or use it in a policy"
      }
    end)
  end

  defp apply_rule(:shadowed_binding, _source, _tokens, ast) do
    find_shadowed_bindings(ast, %{}, [])
  end

  defp apply_rule(:empty_policy, _source, _tokens, ast) do
    ast
    |> Enum.filter(fn
      {:policy, _, {:boolean, true}, _, _} -> true
      _ -> false
    end)
    |> Enum.map(fn {:policy, name, _, _, _} ->
      %{
        severity: :warning,
        code: "W002",
        message: "Policy '#{name}' has a trivial condition (always true)",
        line: 1,
        column: 1,
        suggestion: "Add meaningful conditions to the policy"
      }
    end)
  end

  defp apply_rule(:unreachable_policy, _source, _tokens, ast) do
    policies = Enum.filter(ast, &match?({:policy, _, _, _, _}, &1))

    policies
    |> Enum.with_index()
    |> Enum.flat_map(fn {{:policy, name, _cond, _, meta}, idx} ->
      if has_higher_priority_catch_all?(policies, idx, meta[:priority] || 100) do
        [%{
          severity: :warning,
          code: "W003",
          message: "Policy '#{name}' may be unreachable due to higher-priority catch-all",
          line: 1,
          column: 1,
          suggestion: "Review policy priorities"
        }]
      else
        []
      end
    end)
  end

  defp apply_rule(:hardcoded_credentials, source, _tokens, _ast) do
    patterns = [
      {~r/password\s*=\s*["'][^"']+["']/i, "hardcoded password"},
      {~r/secret\s*=\s*["'][^"']+["']/i, "hardcoded secret"},
      {~r/api_key\s*=\s*["'][^"']+["']/i, "hardcoded API key"},
      {~r/token\s*=\s*["'][^"']+["']/i, "hardcoded token"}
    ]

    source
    |> String.split("\n")
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {line, line_num} ->
      patterns
      |> Enum.filter(fn {regex, _} -> Regex.match?(regex, line) end)
      |> Enum.map(fn {_, desc} ->
        %{
          severity: :error,
          code: "E001",
          message: "Potential #{desc} detected",
          line: line_num,
          column: 1,
          suggestion: "Use environment variables or a secrets manager"
        }
      end)
    end)
  end

  defp apply_rule(:overly_permissive, _source, _tokens, ast) do
    ast
    |> Enum.filter(fn
      {:policy, _, {:boolean, true}, {:accept, _}, %{priority: p}} when p <= 10 -> true
      _ -> false
    end)
    |> Enum.map(fn {:policy, name, _, _, _} ->
      %{
        severity: :warning,
        code: "W004",
        message: "Policy '#{name}' is overly permissive (accepts all with high priority)",
        line: 1,
        column: 1,
        suggestion: "Add specific conditions or lower the priority"
      }
    end)
  end

  defp apply_rule(:missing_priority, _source, _tokens, ast) do
    ast
    |> Enum.filter(fn
      {:policy, _, _, _, meta} -> is_nil(meta[:priority])
      _ -> false
    end)
    |> Enum.map(fn {:policy, name, _, _, _} ->
      %{
        severity: :info,
        code: "I001",
        message: "Policy '#{name}' has no explicit priority",
        line: 1,
        column: 1,
        suggestion: "Add PRIORITY: to make evaluation order explicit"
      }
    end)
  end

  defp apply_rule(:duplicate_policy_name, _source, _tokens, ast) do
    ast
    |> Enum.filter(&match?({:policy, _, _, _, _}, &1))
    |> Enum.map(fn {:policy, name, _, _, _} -> name end)
    |> Enum.frequencies()
    |> Enum.filter(fn {_, count} -> count > 1 end)
    |> Enum.map(fn {name, count} ->
      %{
        severity: :error,
        code: "E002",
        message: "Duplicate policy name '#{name}' (appears #{count} times)",
        line: 1,
        column: 1,
        suggestion: "Use unique names for each policy"
      }
    end)
  end

  defp apply_rule(:long_line, source, _tokens, _ast) do
    max_length = 100

    source
    |> String.split("\n")
    |> Enum.with_index(1)
    |> Enum.filter(fn {line, _} -> String.length(line) > max_length end)
    |> Enum.map(fn {line, line_num} ->
      %{
        severity: :info,
        code: "I002",
        message: "Line exceeds #{max_length} characters (#{String.length(line)})",
        line: line_num,
        column: max_length + 1,
        suggestion: "Break long lines for readability"
      }
    end)
  end

  defp apply_rule(:trailing_whitespace, source, _tokens, _ast) do
    source
    |> String.split("\n")
    |> Enum.with_index(1)
    |> Enum.filter(fn {line, _} -> String.match?(line, ~r/\s+$/) end)
    |> Enum.map(fn {_, line_num} ->
      %{
        severity: :info,
        code: "I003",
        message: "Trailing whitespace",
        line: line_num,
        column: 1,
        suggestion: "Remove trailing whitespace"
      }
    end)
  end

  defp apply_rule(:mixed_indentation, source, _tokens, _ast) do
    lines = String.split(source, "\n")
    has_tabs = Enum.any?(lines, &String.starts_with?(&1, "\t"))
    has_spaces = Enum.any?(lines, &String.match?(&1, ~r/^  /))

    if has_tabs and has_spaces do
      [%{
        severity: :warning,
        code: "W005",
        message: "Mixed tabs and spaces for indentation",
        line: 1,
        column: 1,
        suggestion: "Use consistent indentation (prefer spaces)"
      }]
    else
      []
    end
  end

  defp apply_rule(:undefined_identifier, _source, _tokens, ast) do
    {defined, referenced} = collect_identifiers(ast)

    undefined = MapSet.difference(referenced, defined)

    # Filter out built-ins
    builtins = MapSet.new(["true", "false", "nil", "route", "packet", "request", "context"])
    undefined = MapSet.difference(undefined, builtins)

    undefined
    |> MapSet.to_list()
    |> Enum.map(fn name ->
      %{
        severity: :error,
        code: "E003",
        message: "Undefined identifier '#{name}'",
        line: 1,
        column: 1,
        suggestion: "Define the constant or check for typos"
      }
    end)
  end

  defp apply_rule(:deprecated_syntax, _source, tokens, _ast) do
    deprecated = [
      {:keyword, "ALLOW"} # deprecated in favor of ACCEPT
    ]

    tokens
    |> Enum.filter(fn {type, val, _, _} -> {type, val} in deprecated end)
    |> Enum.map(fn {_, val, line, col} ->
      %{
        severity: :warning,
        code: "W006",
        message: "Deprecated syntax: '#{val}'",
        line: line,
        column: col,
        suggestion: "Use modern syntax"
      }
    end)
  end

  defp apply_rule(_, _, _, _), do: []

  # ============================================================
  # Helpers
  # ============================================================

  defp collect_const_usage(ast) do
    defined = ast
      |> Enum.filter(&match?({:const, _, _}, &1))
      |> Enum.map(fn {:const, name, _} -> {name, 1, 1} end)
      |> MapSet.new()

    used = collect_identifiers_from_expr(ast)

    {defined, used}
  end

  defp collect_identifiers_from_expr(ast) when is_list(ast) do
    Enum.reduce(ast, MapSet.new(), fn node, acc ->
      MapSet.union(acc, collect_identifiers_from_expr(node))
    end)
  end

  defp collect_identifiers_from_expr({:identifier, name}) do
    MapSet.new([name])
  end

  defp collect_identifiers_from_expr({:const, _, value}) do
    collect_identifiers_from_expr(value)
  end

  defp collect_identifiers_from_expr({:policy, _, condition, action, _}) do
    MapSet.union(
      collect_identifiers_from_expr(condition),
      collect_identifiers_from_expr(action)
    )
  end

  defp collect_identifiers_from_expr({:binary_op, _, left, right}) do
    MapSet.union(
      collect_identifiers_from_expr(left),
      collect_identifiers_from_expr(right)
    )
  end

  defp collect_identifiers_from_expr({:comparison, _, left, right}) do
    MapSet.union(
      collect_identifiers_from_expr(left),
      collect_identifiers_from_expr(right)
    )
  end

  defp collect_identifiers_from_expr({:logical_op, _, left, right}) do
    MapSet.union(
      collect_identifiers_from_expr(left),
      collect_identifiers_from_expr(right)
    )
  end

  defp collect_identifiers_from_expr({:call, _, args}) do
    collect_identifiers_from_expr(args)
  end

  defp collect_identifiers_from_expr({:list, elements}) do
    collect_identifiers_from_expr(elements)
  end

  defp collect_identifiers_from_expr({:field_access, expr, _}) do
    collect_identifiers_from_expr(expr)
  end

  defp collect_identifiers_from_expr({:optional_access, expr, _}) do
    collect_identifiers_from_expr(expr)
  end

  defp collect_identifiers_from_expr(_), do: MapSet.new()

  defp find_shadowed_bindings(ast, scope, issues) when is_list(ast) do
    Enum.reduce(ast, issues, fn node, acc ->
      find_shadowed_bindings(node, scope, acc)
    end)
  end

  defp find_shadowed_bindings({:const, name, _}, scope, issues) do
    if Map.has_key?(scope, name) do
      [%{
        severity: :warning,
        code: "W007",
        message: "Constant '#{name}' shadows an earlier binding",
        line: 1,
        column: 1,
        suggestion: "Use a different name to avoid confusion"
      } | issues]
    else
      issues
    end
  end

  defp find_shadowed_bindings(_, _, issues), do: issues

  defp has_higher_priority_catch_all?(policies, current_idx, current_priority) do
    policies
    |> Enum.take(current_idx)
    |> Enum.any?(fn {:policy, _, cond, _, meta} ->
      is_catch_all?(cond) and (meta[:priority] || 100) < current_priority
    end)
  end

  defp is_catch_all?({:boolean, true}), do: true
  defp is_catch_all?(_), do: false

  defp collect_identifiers(ast) do
    defined = ast
      |> Enum.filter(&match?({:const, _, _}, &1))
      |> Enum.map(fn {:const, name, _} -> name end)
      |> MapSet.new()

    referenced = collect_identifiers_from_expr(ast)

    {defined, referenced}
  end

  defp format_severity(:error), do: "error"
  defp format_severity(:warning), do: "warning"
  defp format_severity(:info), do: "info"
end
