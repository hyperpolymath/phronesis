# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Parser.Errors do
  @moduledoc """
  Enhanced error handling for the Phronesis parser (v0.2.x).

  Provides contextual error messages with:
  - Detailed descriptions of what was expected
  - What token was actually found
  - Context about where in the parse tree the error occurred
  - Suggestions for common mistakes
  - Source snippets when available
  """

  @type error_context :: :program | :policy | :condition | :action | :expression |
                         :metadata | :import | :const | :function_call | :arguments

  @type parse_error :: %{
          message: String.t(),
          expected: String.t() | [String.t()],
          found: String.t(),
          context: error_context(),
          line: pos_integer(),
          column: pos_integer(),
          suggestion: String.t() | nil
        }

  @doc """
  Create an enhanced parse error with context.
  """
  @spec error(error_context(), String.t() | [String.t()], tuple() | nil, keyword()) ::
          {:error, {:parse_error, String.t(), pos_integer(), pos_integer(), map()}}
  def error(context, expected, token, opts \\ []) do
    {found, line, col} = extract_token_info(token)
    suggestion = Keyword.get(opts, :suggestion) || suggest_fix(context, expected, found)

    message = build_message(context, expected, found, suggestion)

    details = %{
      expected: expected,
      found: found,
      context: context,
      suggestion: suggestion
    }

    {:error, {:parse_error, message, line, col, details}}
  end

  @doc """
  Format a parse error for display.
  """
  @spec format_error({:parse_error, String.t(), pos_integer(), pos_integer(), map()}) :: String.t()
  def format_error({:parse_error, message, line, col, details}) do
    base = "Parse error at line #{line}, column #{col}: #{message}"

    case details[:suggestion] do
      nil -> base
      suggestion -> "#{base}\n  Suggestion: #{suggestion}"
    end
  end

  def format_error({:parse_error, message, line, col}) do
    "Parse error at line #{line}, column #{col}: #{message}"
  end

  # Extract token information
  defp extract_token_info(nil), do: {"end of input", 0, 0}
  defp extract_token_info({type, value, line, col}), do: {format_token(type, value), line, col}
  defp extract_token_info([{type, value, line, col} | _]), do: {format_token(type, value), line, col}
  defp extract_token_info([]), do: {"end of input", 0, 0}

  # Format token for error messages
  defp format_token(:eof, _), do: "end of input"
  defp format_token(:identifier, name), do: "identifier '#{name}'"
  defp format_token(:integer, value), do: "integer #{value}"
  defp format_token(:float, value), do: "float #{value}"
  defp format_token(:string, value), do: "string \"#{String.slice(value, 0, 20)}...\""
  defp format_token(:ip_address, value), do: "IP address #{value}"
  defp format_token(:ipv6_address, value), do: "IPv6 address #{value}"
  defp format_token(:datetime, value), do: "datetime #{value}"
  defp format_token(type, _), do: "'#{format_keyword(type)}'"

  # Format keyword tokens
  defp format_keyword(:policy), do: "POLICY"
  defp format_keyword(:then), do: "THEN"
  defp format_keyword(:priority), do: "PRIORITY"
  defp format_keyword(:expires), do: "EXPIRES"
  defp format_keyword(:created_by), do: "CREATED_BY"
  defp format_keyword(:const), do: "CONST"
  defp format_keyword(:and), do: "AND"
  defp format_keyword(:or), do: "OR"
  defp format_keyword(:not), do: "NOT"
  defp format_keyword(:execute), do: "EXECUTE"
  defp format_keyword(:report), do: "REPORT"
  defp format_keyword(:reject), do: "REJECT"
  defp format_keyword(:accept), do: "ACCEPT"
  defp format_keyword(:if), do: "IF"
  defp format_keyword(:else), do: "ELSE"
  defp format_keyword(:begin), do: "BEGIN"
  defp format_keyword(:end_block), do: "END"
  defp format_keyword(:import), do: "IMPORT"
  defp format_keyword(:as), do: "AS"
  defp format_keyword(:colon), do: ":"
  defp format_keyword(:comma), do: ","
  defp format_keyword(:dot), do: "."
  defp format_keyword(:lparen), do: "("
  defp format_keyword(:rparen), do: ")"
  defp format_keyword(:lbracket), do: "["
  defp format_keyword(:rbracket), do: "]"
  defp format_keyword(:lbrace), do: "{"
  defp format_keyword(:rbrace), do: "}"
  defp format_keyword(:assign), do: "="
  defp format_keyword(:eq), do: "=="
  defp format_keyword(:neq), do: "!="
  defp format_keyword(:gt), do: ">"
  defp format_keyword(:gte), do: ">="
  defp format_keyword(:lt), do: "<"
  defp format_keyword(:lte), do: "<="
  defp format_keyword(:plus), do: "+"
  defp format_keyword(:minus), do: "-"
  defp format_keyword(:star), do: "*"
  defp format_keyword(:slash), do: "/"
  defp format_keyword(:percent), do: "%"
  defp format_keyword(:in), do: "IN"
  defp format_keyword(:true), do: "true"
  defp format_keyword(:false), do: "false"
  defp format_keyword(:null), do: "null"
  defp format_keyword(:never), do: "never"
  defp format_keyword(other), do: to_string(other)

  # Build error message
  defp build_message(context, expected, found, suggestion) do
    context_str = context_description(context)
    expected_str = format_expected(expected)

    base = "#{context_str}: expected #{expected_str}, but found #{found}"

    if suggestion do
      "#{base}"
    else
      base
    end
  end

  # Context descriptions
  defp context_description(:program), do: "At top level"
  defp context_description(:policy), do: "In policy declaration"
  defp context_description(:condition), do: "In condition"
  defp context_description(:action), do: "In action"
  defp context_description(:expression), do: "In expression"
  defp context_description(:metadata), do: "In policy metadata"
  defp context_description(:import), do: "In import declaration"
  defp context_description(:const), do: "In constant declaration"
  defp context_description(:function_call), do: "In function call"
  defp context_description(:arguments), do: "In argument list"

  # Format expected values
  defp format_expected(expected) when is_list(expected) do
    case expected do
      [single] -> "'#{format_keyword(single)}'"
      [a, b] -> "'#{format_keyword(a)}' or '#{format_keyword(b)}'"
      many -> Enum.map_join(many, ", ", &"'#{format_keyword(&1)}'") |> String.replace(~r/, ([^,]+)$/, ", or \\1")
    end
  end

  defp format_expected(expected) when is_atom(expected) do
    "'#{format_keyword(expected)}'"
  end

  defp format_expected(expected) when is_binary(expected) do
    expected
  end

  # Suggest fixes for common mistakes
  defp suggest_fix(:policy, :colon, found) when found in ["'='", "identifier"] do
    "Policy declarations use ':' not '=' after the name. Example: POLICY my_policy: ..."
  end

  defp suggest_fix(:policy, :then, "'AND'" <> _) do
    "Missing 'THEN' before action. The condition should be followed by 'THEN action'."
  end

  defp suggest_fix(:metadata, :priority, found) when found in ["'THEN'", "identifier"] do
    "Every policy needs a PRIORITY. Add 'PRIORITY: <number>' after the action."
  end

  defp suggest_fix(:action, _, "'{'") do
    "Use 'BEGIN ... END' for blocks, not curly braces."
  end

  defp suggest_fix(:expression, _, "identifier 'and'") do
    "Logical operators must be uppercase: use 'AND' not 'and'."
  end

  defp suggest_fix(:expression, _, "identifier 'or'") do
    "Logical operators must be uppercase: use 'OR' not 'or'."
  end

  defp suggest_fix(:expression, _, "identifier 'not'") do
    "Logical operators must be uppercase: use 'NOT' not 'not'."
  end

  defp suggest_fix(:condition, _, "'='") do
    "Use '==' for comparison, not '='. Single '=' is for assignment in CONST declarations."
  end

  defp suggest_fix(:arguments, :rparen, "end of input") do
    "Missing closing parenthesis ')' in function call."
  end

  defp suggest_fix(_, _, _), do: nil

  @doc """
  Create a simple error (backwards compatible).
  """
  @spec simple_error(String.t(), pos_integer(), pos_integer()) ::
          {:error, {:parse_error, String.t(), pos_integer(), pos_integer()}}
  def simple_error(message, line, col) do
    {:error, {:parse_error, message, line, col}}
  end
end
