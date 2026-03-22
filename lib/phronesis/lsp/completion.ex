# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.LSP.Completion do
  @moduledoc """
  Auto-completion for Phronesis LSP.

  Provides completion suggestions for:
  - Keywords (POLICY, CONST, IMPORT, etc.)
  - Standard library modules and functions
  - Variables in scope
  - Policy names
  """

  alias Phronesis.LSP.TextDocument

  @keywords [
    "POLICY",
    "CONST",
    "IMPORT",
    "IF",
    "THEN",
    "ELSE",
    "AND",
    "OR",
    "NOT",
    "IN",
    "ACCEPT",
    "REJECT",
    "REPORT",
    "EXECUTE",
    "BLOCK",
    "PRIORITY",
    "EXPIRES",
    "CREATED_BY",
    "AS",
    "TEST",
    "SCENARIO",
    "GIVEN",
    "EXPECT"
  ]

  @stdlib_modules [
    "Std.RPKI",
    "Std.BGP",
    "Std.Consensus",
    "Std.Temporal"
  ]

  @stdlib_functions %{
    "Std.RPKI" => [
      {"validate", "(route)", "Validate route against RPKI ROAs"},
      {"check_origin", "(asn, roa_asn)", "Check if origin AS is authorized"},
      {"validation_status", "(status)", "Get validation status as string"}
    ],
    "Std.BGP" => [
      {"extract_as_path", "(route)", "Extract AS path from route"},
      {"get_origin", "(route)", "Get origin AS number"},
      {"path_length", "(route)", "Get AS path length"},
      {"validate_route", "(route)", "Validate route against security checks"},
      {"is_private_asn", "(asn)", "Check if ASN is private/reserved"},
      {"is_bogon_asn", "(asn)", "Check if ASN is bogon"}
    ],
    "Std.Consensus" => [
      {"vote", "(action, agents, threshold)", "Collect votes and check consensus"},
      {"count_approvals", "(votes)", "Count affirmative votes"}
    ],
    "Std.Temporal" => [
      {"now", "()", "Get current UTC timestamp"},
      {"is_expired", "(timestamp, duration)", "Check if timestamp expired"},
      {"within_window", "(start_time, end_time)", "Check if within time window"},
      {"parse", "(timestamp_str)", "Parse ISO8601 timestamp"},
      {"format", "(datetime)", "Format as ISO8601 string"},
      {"duration", "(start_time, end_time)", "Calculate duration in seconds"}
    ]
  }

  @doc """
  Compute completion items for a position in a document.
  """
  def compute(document, position) do
    word = TextDocument.word_at_position(document, position) || ""
    line = TextDocument.get_line(document, position["line"]) || ""

    cond do
      # After "Std." - complete module names
      String.ends_with?(word, "Std.") or String.contains?(line, "Std.") ->
        complete_stdlib_modules(word)

      # After module name - complete functions
      stdlib_module?(word) ->
        complete_stdlib_functions(word)

      # General keyword/stdlib completion
      true ->
        complete_keywords(word) ++ complete_stdlib_modules(word)
    end
  end

  defp complete_keywords(prefix) do
    @keywords
    |> Enum.filter(&String.starts_with?(&1, prefix))
    |> Enum.map(fn keyword ->
      %{
        "label" => keyword,
        "kind" => 14,
        # Keyword
        "detail" => "Keyword",
        "documentation" => keyword_documentation(keyword)
      }
    end)
  end

  defp complete_stdlib_modules(prefix) do
    @stdlib_modules
    |> Enum.filter(&String.starts_with?(&1, prefix))
    |> Enum.map(fn mod ->
      %{
        "label" => mod,
        "kind" => 9,
        # Module
        "detail" => "Standard library module",
        "documentation" => module_documentation(mod)
      }
    end)
  end

  defp complete_stdlib_functions(module_prefix) do
    # Extract module name (e.g., "Std.RPKI" from "Std.RPKI.val")
    module =
      case String.split(module_prefix, ".") do
        [ns, mod | _] -> "#{ns}.#{mod}"
        _ -> module_prefix
      end

    case Map.get(@stdlib_functions, module) do
      nil ->
        []

      functions ->
        Enum.map(functions, fn {name, signature, doc} ->
          %{
            "label" => name,
            "kind" => 3,
            # Function
            "detail" => "#{module}.#{name}#{signature}",
            "documentation" => doc,
            "insertText" => "#{name}(${1})",
            "insertTextFormat" => 2
            # Snippet
          }
        end)
    end
  end

  defp stdlib_module?(word) do
    Enum.any?(@stdlib_modules, &String.starts_with?(word, &1))
  end

  defp keyword_documentation("POLICY"), do: "Define a policy with condition and action"
  defp keyword_documentation("CONST"), do: "Define a constant value"
  defp keyword_documentation("IMPORT"), do: "Import a module"
  defp keyword_documentation("IF"), do: "Conditional expression"
  defp keyword_documentation("THEN"), do: "Policy action clause"
  defp keyword_documentation("ELSE"), do: "Alternative branch"
  defp keyword_documentation("AND"), do: "Logical AND operator"
  defp keyword_documentation("OR"), do: "Logical OR operator"
  defp keyword_documentation("NOT"), do: "Logical NOT operator"
  defp keyword_documentation("IN"), do: "Membership test operator"
  defp keyword_documentation("ACCEPT"), do: "Accept action - allow the situation"
  defp keyword_documentation("REJECT"), do: "Reject action - deny the situation"
  defp keyword_documentation("REPORT"), do: "Report action - log message"
  defp keyword_documentation("EXECUTE"), do: "Execute a function"
  defp keyword_documentation("BLOCK"), do: "Block of multiple actions"
  defp keyword_documentation("PRIORITY"), do: "Policy priority (higher = evaluated first)"
  defp keyword_documentation("EXPIRES"), do: "Policy expiration time"
  defp keyword_documentation("CREATED_BY"), do: "Policy creator identifier"
  defp keyword_documentation("TEST"), do: "Define a test suite"
  defp keyword_documentation("SCENARIO"), do: "Define a test scenario"
  defp keyword_documentation("GIVEN"), do: "Test preconditions"
  defp keyword_documentation("EXPECT"), do: "Expected test outcome"
  defp keyword_documentation(_), do: ""

  defp module_documentation("Std.RPKI"),
    do: "RPKI (Resource Public Key Infrastructure) validation functions"

  defp module_documentation("Std.BGP"), do: "BGP (Border Gateway Protocol) utility functions"

  defp module_documentation("Std.Consensus"),
    do: "Distributed consensus and voting functions"

  defp module_documentation("Std.Temporal"), do: "Time and duration utility functions"
  defp module_documentation(_), do: ""
end
