# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Formatter do
  @moduledoc """
  Code formatter for Phronesis policy language.

  Provides consistent, opinionated formatting of Phronesis source code
  following the language style guidelines.
  """

  alias Phronesis.{Lexer, Parser}

  @indent_size 2
  @max_line_length 100

  @doc """
  Format source code string.

  Returns `{:ok, formatted_source}` or `{:error, reason}`.
  """
  @spec format(String.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def format(source, opts \\ []) do
    indent_size = Keyword.get(opts, :indent_size, @indent_size)
    max_line = Keyword.get(opts, :max_line_length, @max_line_length)

    with {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      formatted = format_ast(ast, %{indent: 0, indent_size: indent_size, max_line: max_line})
      {:ok, formatted}
    end
  end

  @doc """
  Format a file in place.
  """
  @spec format_file(Path.t(), keyword()) :: :ok | {:error, term()}
  def format_file(path, opts \\ []) do
    with {:ok, source} <- File.read(path),
         {:ok, formatted} <- format(source, opts) do
      File.write(path, formatted)
    end
  end

  @doc """
  Check if source is already formatted.
  """
  @spec check(String.t(), keyword()) :: :ok | {:error, :not_formatted}
  def check(source, opts \\ []) do
    case format(source, opts) do
      {:ok, formatted} ->
        if formatted == source, do: :ok, else: {:error, :not_formatted}

      {:error, _} = err ->
        err
    end
  end

  # ============================================================
  # AST Formatting
  # ============================================================

  defp format_ast(statements, ctx) when is_list(statements) do
    statements
    |> Enum.map(&format_statement(&1, ctx))
    |> Enum.join("\n")
    |> String.trim_trailing()
    |> Kernel.<>("\n")
  end

  defp format_statement({:const, name, value}, ctx) do
    indent(ctx) <> "CONST #{name} = #{format_expr(value, ctx)}"
  end

  defp format_statement({:policy, name, condition, action, meta}, ctx) do
    lines = [
      indent(ctx) <> "POLICY #{name}:",
      format_expr(condition, inc_indent(ctx)),
      indent(inc_indent(ctx)) <> "THEN #{format_action(action, ctx)}"
    ]

    meta_lines = format_policy_meta(meta, inc_indent(ctx))
    Enum.join(lines ++ meta_lines, "\n")
  end

  defp format_statement({:module, path, body}, ctx) do
    path_str = Enum.join(path, "::")
    body_formatted = body
      |> Enum.map(&format_statement(&1, inc_indent(ctx)))
      |> Enum.join("\n")

    """
    #{indent(ctx)}MODULE #{path_str}:
    #{body_formatted}
    #{indent(ctx)}END
    """
    |> String.trim_trailing()
  end

  defp format_statement({:import, path}, ctx) do
    indent(ctx) <> "IMPORT #{Enum.join(path, "::")}"
  end

  defp format_statement({:import, path, items}, ctx) do
    items_str = Enum.join(items, ", ")
    indent(ctx) <> "FROM #{Enum.join(path, "::")} IMPORT #{items_str}"
  end

  defp format_statement({:function, name, params, body}, ctx) do
    params_str = Enum.join(params, ", ")
    body_formatted = format_expr(body, inc_indent(ctx))

    """
    #{indent(ctx)}FN #{name}(#{params_str}):
    #{body_formatted}
    #{indent(ctx)}END
    """
    |> String.trim_trailing()
  end

  defp format_statement({:report, expr}, ctx) do
    indent(ctx) <> "REPORT #{format_expr(expr, ctx)}"
  end

  defp format_statement(other, ctx) do
    indent(ctx) <> format_expr(other, ctx)
  end

  # ============================================================
  # Expression Formatting
  # ============================================================

  defp format_expr({:integer, n}, _ctx), do: Integer.to_string(n)
  defp format_expr({:float, n}, _ctx), do: Float.to_string(n)
  defp format_expr({:string, s}, _ctx), do: ~s("#{escape_string(s)}")
  defp format_expr({:boolean, b}, _ctx), do: if(b, do: "true", else: "false")
  defp format_expr({:identifier, name}, _ctx), do: name
  defp format_expr({:atom, name}, _ctx), do: ":#{name}"
  defp format_expr(:nil, _ctx), do: "nil"

  defp format_expr({:ipv4_address, addr}, _ctx), do: addr
  defp format_expr({:ipv6_address, addr}, _ctx), do: addr
  defp format_expr({:cidr, prefix, len}, _ctx), do: "#{prefix}/#{len}"

  defp format_expr({:as_path, segments}, _ctx) do
    segments_str = Enum.map_join(segments, " ", fn
      {:as_seq, asns} -> Enum.join(asns, " ")
      {:as_set, asns} -> "{#{Enum.join(asns, " ")}}"
    end)
    "AS_PATH[#{segments_str}]"
  end

  defp format_expr({:binary_op, op, left, right}, ctx) do
    left_str = format_expr(left, ctx)
    right_str = format_expr(right, ctx)
    op_str = format_operator(op)
    "#{left_str} #{op_str} #{right_str}"
  end

  defp format_expr({:unary_op, op, expr}, ctx) do
    op_str = format_unary_op(op)
    expr_str = format_expr(expr, ctx)
    "#{op_str}#{expr_str}"
  end

  defp format_expr({:comparison, op, left, right}, ctx) do
    left_str = format_expr(left, ctx)
    right_str = format_expr(right, ctx)
    op_str = format_comparison_op(op)
    "#{left_str} #{op_str} #{right_str}"
  end

  defp format_expr({:logical_op, op, left, right}, ctx) do
    left_str = format_expr(left, ctx)
    right_str = format_expr(right, ctx)
    op_str = format_logical_op(op)
    "#{left_str} #{op_str} #{right_str}"
  end

  defp format_expr({:if, condition, then_branch, else_branch}, ctx) do
    cond_str = format_expr(condition, ctx)
    then_str = format_expr(then_branch, inc_indent(ctx))
    else_str = format_expr(else_branch, inc_indent(ctx))

    """
    #{indent(ctx)}IF #{cond_str} THEN
    #{then_str}
    #{indent(ctx)}ELSE
    #{else_str}
    #{indent(ctx)}END
    """
    |> String.trim()
  end

  defp format_expr({:list, elements}, ctx) do
    if length(elements) <= 3 do
      "[#{Enum.map_join(elements, ", ", &format_expr(&1, ctx))}]"
    else
      inner = elements
        |> Enum.map(&(indent(inc_indent(ctx)) <> format_expr(&1, ctx)))
        |> Enum.join(",\n")
      "[\n#{inner}\n#{indent(ctx)}]"
    end
  end

  defp format_expr({:map, pairs}, ctx) do
    if length(pairs) <= 2 do
      pairs_str = Enum.map_join(pairs, ", ", fn {k, v} ->
        "#{format_expr(k, ctx)}: #{format_expr(v, ctx)}"
      end)
      "{#{pairs_str}}"
    else
      inner = pairs
        |> Enum.map(fn {k, v} ->
          indent(inc_indent(ctx)) <> "#{format_expr(k, ctx)}: #{format_expr(v, ctx)}"
        end)
        |> Enum.join(",\n")
      "{\n#{inner}\n#{indent(ctx)}}"
    end
  end

  defp format_expr({:call, name, args}, ctx) do
    args_str = Enum.map_join(args, ", ", &format_expr(&1, ctx))
    "#{name}(#{args_str})"
  end

  defp format_expr({:module_call, path, args}, ctx) do
    path_str = Enum.join(path, "::")
    args_str = Enum.map_join(args, ", ", &format_expr(&1, ctx))
    "#{path_str}(#{args_str})"
  end

  defp format_expr({:field_access, expr, field}, ctx) do
    "#{format_expr(expr, ctx)}.#{field}"
  end

  defp format_expr({:optional_access, expr, field}, ctx) do
    "#{format_expr(expr, ctx)}?.#{field}"
  end

  defp format_expr({:index, expr, index}, ctx) do
    "#{format_expr(expr, ctx)}[#{format_expr(index, ctx)}]"
  end

  defp format_expr({:interpolated_string, parts}, ctx) do
    formatted = Enum.map_join(parts, "", fn
      {:string, s} -> escape_string(s)
      {:expr, e} -> "${#{format_expr(e, ctx)}}"
    end)
    ~s("#{formatted}")
  end

  defp format_expr({:lambda, params, body}, ctx) do
    params_str = Enum.join(params, ", ")
    body_str = format_expr(body, ctx)
    "(#{params_str}) => #{body_str}"
  end

  defp format_expr({:range, from, to}, ctx) do
    "#{format_expr(from, ctx)}..#{format_expr(to, ctx)}"
  end

  defp format_expr(other, _ctx) when is_binary(other), do: other
  defp format_expr(other, _ctx), do: inspect(other)

  # ============================================================
  # Action Formatting
  # ============================================================

  defp format_action({:accept, args}, ctx) do
    if args == [] do
      "ACCEPT()"
    else
      "ACCEPT(#{Enum.map_join(args, ", ", &format_expr(&1, ctx))})"
    end
  end

  defp format_action({:reject, args}, ctx) do
    if args == [] do
      "REJECT()"
    else
      "REJECT(#{Enum.map_join(args, ", ", &format_expr(&1, ctx))})"
    end
  end

  defp format_action({:execute, name, args}, ctx) do
    args_str = Enum.map_join(args, ", ", &format_expr(&1, ctx))
    "EXECUTE(#{name}, #{args_str})"
  end

  defp format_action({:log, level, msg}, ctx) do
    "LOG(#{level}, #{format_expr(msg, ctx)})"
  end

  defp format_action(other, ctx), do: format_expr(other, ctx)

  # ============================================================
  # Policy Metadata
  # ============================================================

  defp format_policy_meta(meta, ctx) do
    lines = []

    lines = if meta[:priority] do
      lines ++ [indent(ctx) <> "PRIORITY: #{meta[:priority]}"]
    else
      lines
    end

    lines = if meta[:expires] do
      exp = case meta[:expires] do
        :never -> "never"
        dt -> DateTime.to_iso8601(dt)
      end
      lines ++ [indent(ctx) <> "EXPIRES: #{exp}"]
    else
      lines
    end

    lines = if meta[:created_by] do
      lines ++ [indent(ctx) <> "CREATED_BY: #{meta[:created_by]}"]
    else
      lines
    end

    lines
  end

  # ============================================================
  # Helpers
  # ============================================================

  defp indent(%{indent: n, indent_size: size}) do
    String.duplicate(" ", n * size)
  end

  defp inc_indent(ctx) do
    %{ctx | indent: ctx.indent + 1}
  end

  defp escape_string(s) do
    s
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
    |> String.replace("\t", "\\t")
  end

  defp format_operator(:add), do: "+"
  defp format_operator(:sub), do: "-"
  defp format_operator(:mul), do: "*"
  defp format_operator(:div), do: "/"
  defp format_operator(:mod), do: "%"
  defp format_operator(:band), do: "&"
  defp format_operator(:bor), do: "|"
  defp format_operator(:bxor), do: "^"
  defp format_operator(:concat), do: "++"
  defp format_operator(op), do: to_string(op)

  defp format_unary_op(:neg), do: "-"
  defp format_unary_op(:not), do: "NOT "
  defp format_unary_op(:bnot), do: "~"
  defp format_unary_op(op), do: to_string(op)

  defp format_comparison_op(:eq), do: "=="
  defp format_comparison_op(:ne), do: "!="
  defp format_comparison_op(:lt), do: "<"
  defp format_comparison_op(:le), do: "<="
  defp format_comparison_op(:gt), do: ">"
  defp format_comparison_op(:ge), do: ">="
  defp format_comparison_op(:in), do: "IN"
  defp format_comparison_op(:contains), do: "CONTAINS"
  defp format_comparison_op(:matches), do: "MATCHES"
  defp format_comparison_op(:overlaps), do: "OVERLAPS"
  defp format_comparison_op(op), do: to_string(op)

  defp format_logical_op(:and), do: "AND"
  defp format_logical_op(:or), do: "OR"
  defp format_logical_op(:xor), do: "XOR"
  defp format_logical_op(op), do: to_string(op)
end
