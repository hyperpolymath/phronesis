# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Diagnostics.Reporter do
  @moduledoc """
  Diagnostic reporter for collecting and displaying diagnostics.

  Provides utilities for batching diagnostics, formatting reports,
  and exporting to different formats (text, JSON).
  """

  alias Phronesis.Diagnostics

  @type report :: %{
          file: String.t(),
          diagnostics: [Diagnostics.diagnostic()],
          error_count: integer(),
          warning_count: integer(),
          info_count: integer(),
          hint_count: integer()
        }

  @doc """
  Create a new diagnostic report.
  """
  def new(file) do
    %{
      file: file,
      diagnostics: [],
      error_count: 0,
      warning_count: 0,
      info_count: 0,
      hint_count: 0
    }
  end

  @doc """
  Add a diagnostic to the report.
  """
  def add(report, diagnostic) do
    updated_report = %{
      report
      | diagnostics: [diagnostic | report.diagnostics]
    }

    increment_count(updated_report, diagnostic.severity)
  end

  @doc """
  Add multiple diagnostics to the report.
  """
  def add_many(report, diagnostics) do
    Enum.reduce(diagnostics, report, fn diagnostic, acc ->
      add(acc, diagnostic)
    end)
  end

  @doc """
  Check if the report has errors.
  """
  def has_errors?(report) do
    report.error_count > 0
  end

  @doc """
  Check if the report has warnings.
  """
  def has_warnings?(report) do
    report.warning_count > 0
  end

  @doc """
  Get diagnostics by severity.
  """
  def by_severity(report, severity) do
    Enum.filter(report.diagnostics, fn d -> d.severity == severity end)
  end

  @doc """
  Sort diagnostics by location.
  """
  def sort_by_location(report) do
    sorted_diagnostics =
      Enum.sort_by(report.diagnostics, fn d ->
        {d.location.line, d.location.column}
      end)

    %{report | diagnostics: sorted_diagnostics}
  end

  @doc """
  Format the report for display.
  """
  def format(report, opts \\ []) do
    use_color = Keyword.get(opts, :color, true)
    sorted_report = sort_by_location(report)

    diagnostics_output =
      sorted_report.diagnostics
      |> Enum.reverse()
      |> Diagnostics.format_many(opts)

    summary = format_summary(sorted_report, use_color)

    if diagnostics_output == "" do
      summary
    else
      diagnostics_output <> "\n\n" <> summary
    end
  end

  @doc """
  Format the report summary.
  """
  def format_summary(report, use_color \\ true) do
    parts = []

    parts =
      if report.error_count > 0 do
        error_text = pluralize("error", report.error_count)

        colored_text =
          if use_color do
            "\e[31m\e[1m#{report.error_count} #{error_text}\e[0m"
          else
            "#{report.error_count} #{error_text}"
          end

        parts ++ [colored_text]
      else
        parts
      end

    parts =
      if report.warning_count > 0 do
        warning_text = pluralize("warning", report.warning_count)

        colored_text =
          if use_color do
            "\e[33m\e[1m#{report.warning_count} #{warning_text}\e[0m"
          else
            "#{report.warning_count} #{warning_text}"
          end

        parts ++ [colored_text]
      else
        parts
      end

    parts =
      if report.info_count > 0 do
        info_text = pluralize("info", report.info_count)

        colored_text =
          if use_color do
            "\e[34m#{report.info_count} #{info_text}\e[0m"
          else
            "#{report.info_count} #{info_text}"
          end

        parts ++ [colored_text]
      else
        parts
      end

    if parts == [] do
      if use_color do
        "\e[32m\e[1m✓ No issues found\e[0m"
      else
        "✓ No issues found"
      end
    else
      Enum.join(parts, ", ")
    end
  end

  @doc """
  Export report to JSON.
  """
  def to_json(report) do
    sorted_report = sort_by_location(report)

    data = %{
      file: sorted_report.file,
      summary: %{
        errors: sorted_report.error_count,
        warnings: sorted_report.warning_count,
        info: sorted_report.info_count,
        hints: sorted_report.hint_count
      },
      diagnostics:
        Enum.map(sorted_report.diagnostics, fn d ->
          %{
            code: d.code,
            severity: to_string(d.severity),
            message: d.message,
            location: %{
              file: d.location.file,
              line: d.location.line,
              column: d.location.column
            },
            suggestion: d.suggestion,
            help: d.help,
            related: d.related
          }
        end)
    }

    Jason.encode!(data, pretty: true)
  end

  @doc """
  Export report to simple text (no colors).
  """
  def to_text(report) do
    format(report, color: false)
  end

  @doc """
  Create a report from lexer errors.
  """
  def from_lexer_errors(file, errors, source_lines) do
    report = new(file)

    diagnostics =
      Enum.map(errors, fn {:error, message, line, column} ->
        context = get_context(source_lines, line)

        Diagnostics.lexer_error(message, file, line, column, context: context)
      end)

    add_many(report, diagnostics)
  end

  @doc """
  Create a report from parser errors.
  """
  def from_parser_errors(file, errors, source_lines) do
    report = new(file)

    diagnostics =
      Enum.map(errors, fn {:error, message, line, column} ->
        context = get_context(source_lines, line)

        Diagnostics.parser_error(message, file, line, column, context: context)
      end)

    add_many(report, diagnostics)
  end

  @doc """
  Create a report from analyzer issues.
  """
  def from_analyzer_issues(file, issues) do
    report = new(file)

    diagnostics =
      Enum.map(issues, fn issue ->
        location = %{
          file: issue.file || file,
          line: issue.line || 1,
          column: issue.column || 1
        }

        Diagnostics.new(
          issue.code || "W0000",
          issue.severity,
          issue.message,
          location,
          context: issue.context,
          suggestion: issue.suggestion,
          help: issue.help
        )
      end)

    add_many(report, diagnostics)
  end

  # Private helper functions

  defp increment_count(report, :error) do
    %{report | error_count: report.error_count + 1}
  end

  defp increment_count(report, :warning) do
    %{report | warning_count: report.warning_count + 1}
  end

  defp increment_count(report, :info) do
    %{report | info_count: report.info_count + 1}
  end

  defp increment_count(report, :hint) do
    %{report | hint_count: report.hint_count + 1}
  end

  defp pluralize(word, 1), do: word
  defp pluralize(word, _), do: "#{word}s"

  defp get_context(source_lines, line) when is_list(source_lines) do
    Enum.at(source_lines, line - 1, "")
  end

  defp get_context(source, line) when is_binary(source) do
    source
    |> String.split("\n")
    |> get_context(line)
  end

  defp get_context(_, _), do: nil
end
