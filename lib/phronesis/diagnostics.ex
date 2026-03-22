# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Diagnostics do
  @moduledoc """
  Enhanced error reporting and diagnostics for Phronesis.

  Provides colorized error messages with source context, suggestions,
  error codes, and help text for improved developer experience.
  """

  @type severity :: :error | :warning | :info | :hint
  @type location :: %{file: String.t(), line: integer(), column: integer()}
  @type diagnostic :: %{
          code: String.t(),
          severity: severity(),
          message: String.t(),
          location: location(),
          context: String.t() | nil,
          suggestion: String.t() | nil,
          help: String.t() | nil,
          related: [String.t()]
        }

  # ANSI color codes
  @colors %{
    red: "\e[31m",
    yellow: "\e[33m",
    blue: "\e[34m",
    cyan: "\e[36m",
    green: "\e[32m",
    bold: "\e[1m",
    reset: "\e[0m"
  }

  @doc """
  Create a new diagnostic.
  """
  def new(code, severity, message, location, opts \\ []) do
    %{
      code: code,
      severity: severity,
      message: message,
      location: location,
      context: Keyword.get(opts, :context),
      suggestion: Keyword.get(opts, :suggestion),
      help: Keyword.get(opts, :help),
      related: Keyword.get(opts, :related, [])
    }
  end

  @doc """
  Format a diagnostic for display.
  """
  def format(diagnostic, opts \\ []) do
    use_color = Keyword.get(opts, :color, true)
    show_context = Keyword.get(opts, :context, true)

    parts = [
      format_header(diagnostic, use_color),
      format_location(diagnostic, use_color)
    ]

    parts =
      if show_context && diagnostic.context do
        parts ++ [format_context(diagnostic, use_color)]
      else
        parts
      end

    parts =
      if diagnostic.suggestion do
        parts ++ [format_suggestion(diagnostic, use_color)]
      else
        parts
      end

    parts =
      if diagnostic.help do
        parts ++ [format_help(diagnostic, use_color)]
      else
        parts
      end

    parts =
      if diagnostic.related != [] do
        parts ++ [format_related(diagnostic, use_color)]
      else
        parts
      end

    Enum.join(parts, "\n")
  end

  @doc """
  Format multiple diagnostics.
  """
  def format_many(diagnostics, opts \\ []) do
    diagnostics
    |> Enum.map(&format(&1, opts))
    |> Enum.join("\n\n")
  end

  @doc """
  Create a lexer error diagnostic.
  """
  def lexer_error(message, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}

    new("E0001", :error, message, location,
      context: Keyword.get(opts, :context),
      help: "Check the syntax of your policy file."
    )
  end

  @doc """
  Create a parser error diagnostic.
  """
  def parser_error(message, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}

    new("E0002", :error, message, location,
      context: Keyword.get(opts, :context),
      help: "Ensure your policy follows the correct syntax structure."
    )
  end

  @doc """
  Create an undefined variable error diagnostic.
  """
  def undefined_variable(var_name, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}
    similar = Keyword.get(opts, :similar)

    suggestion =
      if similar do
        "Did you mean '#{similar}'?"
      else
        nil
      end

    new("E0042", :error, "undefined variable '#{var_name}'", location,
      context: Keyword.get(opts, :context),
      suggestion: suggestion,
      help: "Variables must be defined before use. Check for typos in variable names."
    )
  end

  @doc """
  Create an undefined constant error diagnostic.
  """
  def undefined_constant(const_name, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}
    similar = Keyword.get(opts, :similar)

    suggestion =
      if similar do
        "Did you mean '#{similar}'?"
      else
        nil
      end

    new("E0043", :error, "undefined constant '#{const_name}'", location,
      context: Keyword.get(opts, :context),
      suggestion: suggestion,
      help: "Constants must be declared with CONST before use."
    )
  end

  @doc """
  Create a type error diagnostic.
  """
  def type_error(expected, got, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}

    message = "type mismatch: expected #{expected}, got #{got}"

    new("E0100", :error, message, location,
      context: Keyword.get(opts, :context),
      help: "Check the types of values in your expressions."
    )
  end

  @doc """
  Create an invalid consensus threshold warning.
  """
  def invalid_threshold(value, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}

    message = "consensus threshold must be between 0.0 and 1.0, got #{value}"

    new("W0200", :warning, message, location,
      context: Keyword.get(opts, :context),
      suggestion: "Use a value between 0.0 (0%) and 1.0 (100%).",
      help: "Consensus thresholds represent the fraction of nodes required to agree."
    )
  end

  @doc """
  Create a dead code warning.
  """
  def dead_code(policy_name, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}

    message = "policy '#{policy_name}' has unreachable condition (always false)"

    new("W0300", :warning, message, location,
      context: Keyword.get(opts, :context),
      suggestion: "Remove or fix the condition logic.",
      help: "Dead code will never execute and can be removed."
    )
  end

  @doc """
  Create an unused import warning.
  """
  def unused_import(module_name, file, line, column, opts \\ []) do
    location = %{file: file, line: line, column: column}

    message = "unused import '#{module_name}'"

    new("W0400", :warning, message, location,
      context: Keyword.get(opts, :context),
      suggestion: "Remove the unused IMPORT statement.",
      help: "Remove imports that are not used in your policy file."
    )
  end

  # Private formatting functions

  defp format_header(diagnostic, use_color) do
    severity_label = format_severity(diagnostic.severity, use_color)
    code = if use_color, do: color(:cyan, "[#{diagnostic.code}]"), else: "[#{diagnostic.code}]"

    "#{severity_label}#{code}: #{diagnostic.message}"
  end

  defp format_severity(severity, use_color) do
    case severity do
      :error ->
        if use_color, do: color(:red, "error", bold: true), else: "error"

      :warning ->
        if use_color, do: color(:yellow, "warning", bold: true), else: "warning"

      :info ->
        if use_color, do: color(:blue, "info", bold: true), else: "info"

      :hint ->
        if use_color, do: color(:cyan, "hint", bold: true), else: "hint"
    end
  end

  defp format_location(diagnostic, use_color) do
    loc = diagnostic.location
    arrow = if use_color, do: color(:blue, "-->"), else: "-->"

    "  #{arrow} #{loc.file}:#{loc.line}:#{loc.column}"
  end

  defp format_context(diagnostic, use_color) do
    loc = diagnostic.location
    context_lines = String.split(diagnostic.context, "\n")

    # Show line with error highlighted
    line_num = String.pad_leading(Integer.to_string(loc.line), 4)
    pipe = if use_color, do: color(:blue, "|"), else: "|"

    context_str =
      context_lines
      |> Enum.with_index()
      |> Enum.map(fn {line, idx} ->
        if idx == 0 do
          # Main line with error
          "#{line_num} #{pipe} #{line}\n" <>
            "     #{pipe} #{String.duplicate(" ", loc.column - 1)}#{highlight_error(use_color)}"
        else
          # Additional context lines
          next_line_num = String.pad_leading(Integer.to_string(loc.line + idx), 4)
          "#{next_line_num} #{pipe} #{line}"
        end
      end)
      |> Enum.join("\n")

    "     #{pipe}\n#{context_str}"
  end

  defp highlight_error(use_color) do
    if use_color do
      color(:red, "^", bold: true) <> color(:red, " not found in this scope")
    else
      "^ not found in this scope"
    end
  end

  defp format_suggestion(diagnostic, use_color) do
    help_label = if use_color, do: color(:green, "help:", bold: true), else: "help:"
    "  #{help_label} #{diagnostic.suggestion}"
  end

  defp format_help(diagnostic, use_color) do
    note_label = if use_color, do: color(:cyan, "note:", bold: true), else: "note:"
    "  #{note_label} #{diagnostic.help}"
  end

  defp format_related(diagnostic, use_color) do
    related_label = if use_color, do: color(:cyan, "related:", bold: true), else: "related:"

    related_items = Enum.map(diagnostic.related, fn item -> "    - #{item}" end)

    "  #{related_label}\n" <> Enum.join(related_items, "\n")
  end

  defp color(color_name, text, opts \\ []) do
    bold = Keyword.get(opts, :bold, false)

    prefix =
      if bold do
        @colors[:bold] <> @colors[color_name]
      else
        @colors[color_name]
      end

    prefix <> text <> @colors[:reset]
  end
end
