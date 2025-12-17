# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Parser do
  @moduledoc """
  Recursive descent parser for the Phronesis policy language.

  This is an LL(1) parser - all constructs use distinct leading tokens,
  requiring no backtracking. Linear parsing time.

  ## Grammar

  The parser implements the following grammar (~40 lines of EBNF):

      Program        ::= { Declaration }
      Declaration    ::= PolicyDecl | ImportDecl | ConstDecl
      PolicyDecl     ::= "POLICY" Identifier ":" Condition "THEN" Action PolicyMetadata
      ...

  See the grammar specification for the complete EBNF.

  ## Error Recovery (v0.2.x)

  The parser provides detailed, contextual error messages including:
  - What was expected vs what was found
  - Where in the parse tree the error occurred
  - Suggestions for common mistakes
  - Source location for IDE integration
  """

  alias Phronesis.{Token, AST}
  alias Phronesis.Parser.Errors

  @type tokens :: [Token.t()]
  @type parse_result :: {:ok, AST.program()} | {:error, term()}

  @doc """
  Parse a list of tokens into an AST.

  ## Examples

      iex> tokens = [{:const, "CONST", 1, 1}, {:identifier, "x", 1, 7}, ...]
      iex> Phronesis.Parser.parse(tokens)
      {:ok, [{:const, "x", {:literal, :integer, 42}}]}
  """
  @spec parse(tokens()) :: parse_result()
  def parse(tokens) when is_list(tokens) do
    case parse_program(tokens, []) do
      {:ok, ast, [{:eof, _, _, _}]} ->
        {:ok, Enum.reverse(ast)}

      {:ok, _ast, [token | _]} ->
        {_, _, line, col} = token
        {:error, {:parse_error, "unexpected token after program", line, col}}

      {:error, _} = error ->
        error
    end
  end

  # Program ::= { Declaration }
  defp parse_program([{:eof, _, _, _} | _] = tokens, acc) do
    {:ok, acc, tokens}
  end

  defp parse_program(tokens, acc) do
    case parse_declaration(tokens) do
      {:ok, decl, rest} ->
        parse_program(rest, [decl | acc])

      {:error, _} = error ->
        error
    end
  end

  # Declaration ::= PolicyDecl | ImportDecl | ConstDecl
  defp parse_declaration([{:policy, _, _, _} | _] = tokens) do
    parse_policy(tokens)
  end

  defp parse_declaration([{:import, _, _, _} | _] = tokens) do
    parse_import(tokens)
  end

  defp parse_declaration([{:const, _, _, _} | _] = tokens) do
    parse_const(tokens)
  end

  defp parse_declaration([token | _]) do
    Errors.error(:program, [:policy, :import, :const], token,
      suggestion: "A program consists of POLICY, IMPORT, and CONST declarations")
  end

  # PolicyDecl ::= "POLICY" Identifier ":" Condition "THEN" Action PolicyMetadata
  defp parse_policy([{:policy, _, _, _} | rest]) do
    with {:ok, name, rest} <- expect_identifier(rest),
         {:ok, rest} <- expect(:colon, rest),
         {:ok, condition, rest} <- parse_logical_expr(rest),
         {:ok, rest} <- expect(:then, rest),
         {:ok, action, rest} <- parse_action(rest),
         {:ok, metadata, rest} <- parse_metadata(rest) do
      {:ok, AST.policy(name, condition, action, metadata), rest}
    end
  end

  # PolicyMetadata ::= "PRIORITY:" Integer [ "EXPIRES:" ... ] [ "CREATED_BY:" ... ]
  defp parse_metadata(tokens) do
    with {:ok, rest} <- expect(:priority, tokens),
         {:ok, rest} <- expect(:colon, rest),
         {:ok, priority, rest} <- expect_integer(rest),
         {:ok, expires, rest} <- parse_optional_expires(rest),
         {:ok, created_by, rest} <- parse_optional_created_by(rest) do
      {:ok, AST.metadata(priority: priority, expires: expires, created_by: created_by), rest}
    end
  end

  defp parse_optional_expires([{:expires, _, _, _} | rest]) do
    with {:ok, rest} <- expect(:colon, rest) do
      case rest do
        [{:never, _, _, _} | rest] ->
          {:ok, :never, rest}

        [{:datetime, value, _, _} | rest] ->
          {:ok, value, rest}

        [{_, _, line, col} | _] ->
          {:error, {:parse_error, "expected 'never' or datetime", line, col}}
      end
    end
  end

  defp parse_optional_expires(tokens), do: {:ok, :never, tokens}

  defp parse_optional_created_by([{:created_by, _, _, _} | rest]) do
    with {:ok, rest} <- expect(:colon, rest),
         {:ok, name, rest} <- expect_identifier(rest) do
      {:ok, name, rest}
    end
  end

  defp parse_optional_created_by(tokens), do: {:ok, nil, tokens}

  # ImportDecl ::= "IMPORT" ModulePath [ "AS" Identifier ]
  defp parse_import([{:import, _, _, _} | rest]) do
    with {:ok, path, rest} <- parse_module_path(rest),
         {:ok, alias_name, rest} <- parse_optional_alias(rest) do
      {:ok, AST.import_decl(path, alias_name), rest}
    end
  end

  defp parse_optional_alias([{:as, _, _, _} | rest]) do
    expect_identifier(rest)
  end

  defp parse_optional_alias(tokens), do: {:ok, nil, tokens}

  # ConstDecl ::= "CONST" Identifier "=" Expression
  # Note: We use parse_logical_expr to allow boolean expressions in constants
  defp parse_const([{:const, _, _, _} | rest]) do
    with {:ok, name, rest} <- expect_identifier(rest),
         {:ok, rest} <- expect(:assign, rest),
         {:ok, value, rest} <- parse_logical_expr(rest) do
      {:ok, AST.const_decl(name, value), rest}
    end
  end

  # ModulePath ::= Identifier { "." Identifier }
  defp parse_module_path(tokens) do
    with {:ok, first, rest} <- expect_identifier(tokens) do
      parse_module_path_rest(rest, [first])
    end
  end

  defp parse_module_path_rest([{:dot, _, _, _} | rest], acc) do
    with {:ok, name, rest} <- expect_identifier(rest) do
      parse_module_path_rest(rest, [name | acc])
    end
  end

  defp parse_module_path_rest(tokens, acc) do
    {:ok, Enum.reverse(acc), tokens}
  end

  # LogicalExpr ::= ComparisonExpr { ( "AND" | "OR" ) ComparisonExpr }
  defp parse_logical_expr(tokens) do
    with {:ok, left, rest} <- parse_comparison_expr(tokens) do
      parse_logical_expr_rest(rest, left)
    end
  end

  defp parse_logical_expr_rest([{:and, _, _, _} | rest], left) do
    with {:ok, right, rest} <- parse_comparison_expr(rest) do
      parse_logical_expr_rest(rest, AST.binary_op(:and, left, right))
    end
  end

  defp parse_logical_expr_rest([{:or, _, _, _} | rest], left) do
    with {:ok, right, rest} <- parse_comparison_expr(rest) do
      parse_logical_expr_rest(rest, AST.binary_op(:or, left, right))
    end
  end

  defp parse_logical_expr_rest(tokens, expr) do
    {:ok, expr, tokens}
  end

  # ComparisonExpr ::= Expression RelOp Expression | "NOT" ComparisonExpr
  # Note: Parenthesized logical expressions are handled via nested comparisons
  # e.g., (x == 1) AND (y == 2) - each comparison is parenthesized in Factor
  defp parse_comparison_expr([{:not, _, _, _} | rest]) do
    with {:ok, expr, rest} <- parse_comparison_expr(rest) do
      {:ok, AST.unary_op(:not, expr), rest}
    end
  end

  defp parse_comparison_expr(tokens) do
    with {:ok, left, rest} <- parse_expression(tokens) do
      case rest do
        [{op, _, _, _} | rest] when op in [:eq, :neq, :gt, :gte, :lt, :lte] ->
          with {:ok, right, rest} <- parse_expression(rest) do
            {:ok, AST.comparison(op, left, right), rest}
          end

        [{:in, _, _, _} | rest] ->
          with {:ok, right, rest} <- parse_expression(rest) do
            {:ok, AST.comparison(:in, left, right), rest}
          end

        _ ->
          {:ok, left, rest}
      end
    end
  end

  # Expression ::= Term { ( "+" | "-" ) Term }
  defp parse_expression(tokens) do
    with {:ok, left, rest} <- parse_term(tokens) do
      parse_expression_rest(rest, left)
    end
  end

  defp parse_expression_rest([{:plus, _, _, _} | rest], left) do
    with {:ok, right, rest} <- parse_term(rest) do
      parse_expression_rest(rest, AST.binary_op(:add, left, right))
    end
  end

  defp parse_expression_rest([{:minus, _, _, _} | rest], left) do
    with {:ok, right, rest} <- parse_term(rest) do
      parse_expression_rest(rest, AST.binary_op(:sub, left, right))
    end
  end

  defp parse_expression_rest(tokens, expr) do
    {:ok, expr, tokens}
  end

  # Term ::= Factor { ( "*" | "/" ) Factor }
  defp parse_term(tokens) do
    with {:ok, left, rest} <- parse_factor(tokens) do
      parse_term_rest(rest, left)
    end
  end

  defp parse_term_rest([{:star, _, _, _} | rest], left) do
    with {:ok, right, rest} <- parse_factor(rest) do
      parse_term_rest(rest, AST.binary_op(:mul, left, right))
    end
  end

  defp parse_term_rest([{:slash, _, _, _} | rest], left) do
    with {:ok, right, rest} <- parse_factor(rest) do
      parse_term_rest(rest, AST.binary_op(:div, left, right))
    end
  end

  defp parse_term_rest(tokens, expr) do
    {:ok, expr, tokens}
  end

  # Factor ::= Literal | Identifier | ModuleCall | "(" Expression ")" | "-" Factor
  defp parse_factor([{:minus, _, _, _} | rest]) do
    with {:ok, expr, rest} <- parse_factor(rest) do
      {:ok, AST.unary_op(:neg, expr), rest}
    end
  end

  defp parse_factor([{:lparen, _, _, _} | rest]) do
    with {:ok, expr, rest} <- parse_expression(rest),
         {:ok, rest} <- expect(:rparen, rest) do
      {:ok, expr, rest}
    end
  end

  # Integer literals (v0.2.x: hex, binary, octal)
  defp parse_factor([{:integer, value, _, _} | rest]) do
    {:ok, AST.literal(:integer, value), rest}
  end

  defp parse_factor([{:hex_integer, value, _, _} | rest]) do
    {:ok, AST.literal(:integer, value), rest}
  end

  defp parse_factor([{:binary_integer, value, _, _} | rest]) do
    {:ok, AST.literal(:integer, value), rest}
  end

  defp parse_factor([{:octal_integer, value, _, _} | rest]) do
    {:ok, AST.literal(:integer, value), rest}
  end

  defp parse_factor([{:float, value, _, _} | rest]) do
    {:ok, AST.literal(:float, value), rest}
  end

  # String literals (v0.2.x: raw, multiline, interpolated)
  defp parse_factor([{:string, value, _, _} | rest]) do
    {:ok, AST.literal(:string, value), rest}
  end

  defp parse_factor([{:raw_string, value, _, _} | rest]) do
    {:ok, AST.literal(:string, value), rest}
  end

  defp parse_factor([{:multiline_string, value, _, _} | rest]) do
    {:ok, AST.literal(:string, value), rest}
  end

  defp parse_factor([{:interpolated_string, parts, _, _} | rest]) do
    {:ok, AST.interpolated_string(parts), rest}
  end

  # IP address literals (v0.2.x: IPv6)
  defp parse_factor([{:ip_address, value, _, _} | rest]) do
    {:ok, AST.literal(:ip_address, value), rest}
  end

  defp parse_factor([{:ipv6_address, value, _, _} | rest]) do
    {:ok, AST.literal(:ipv6_address, value), rest}
  end

  defp parse_factor([{:datetime, value, _, _} | rest]) do
    {:ok, AST.literal(:datetime, value), rest}
  end

  defp parse_factor([{:true, _, _, _} | rest]) do
    {:ok, AST.literal(:boolean, true), rest}
  end

  defp parse_factor([{:false, _, _, _} | rest]) do
    {:ok, AST.literal(:boolean, false), rest}
  end

  # v0.2.x: null literal
  defp parse_factor([{:null, _, _, _} | rest]) do
    {:ok, AST.literal(:null, nil), rest}
  end

  # Identifier or ModuleCall
  defp parse_factor([{:identifier, name, _, _} | rest]) do
    case rest do
      [{:dot, _, _, _} | _] ->
        # Could be module call (Std.RPKI.validate(...))
        parse_possible_module_call([{:identifier, name, 0, 0} | rest])

      [{:lparen, _, _, _} | _] ->
        # Function call
        parse_function_call(name, rest)

      _ ->
        {:ok, AST.identifier(name), rest}
    end
  end

  defp parse_factor([token | _]) do
    Errors.error(:expression, "a value (number, string, identifier, or parenthesized expression)", token)
  end

  defp parse_factor([]) do
    Errors.error(:expression, "an expression", nil)
  end

  defp parse_possible_module_call(tokens) do
    with {:ok, path, rest} <- parse_module_path(tokens) do
      case rest do
        [{:lparen, _, _, _} | rest] ->
          with {:ok, args, rest} <- parse_arguments(rest),
               {:ok, rest} <- expect(:rparen, rest) do
            {:ok, AST.module_call(path, args), rest}
          end

        _ ->
          # Just an identifier with dots (shouldn't happen in valid code)
          {:ok, AST.identifier(Enum.join(path, ".")), rest}
      end
    end
  end

  defp parse_function_call(name, [{:lparen, _, _, _} | rest]) do
    with {:ok, args, rest} <- parse_arguments(rest),
         {:ok, rest} <- expect(:rparen, rest) do
      {:ok, AST.module_call([name], args), rest}
    end
  end

  # Arguments ::= [ Expression { "," Expression } ]
  defp parse_arguments([{:rparen, _, _, _} | _] = tokens) do
    {:ok, [], tokens}
  end

  defp parse_arguments(tokens) do
    with {:ok, first, rest} <- parse_expression_or_named_arg(tokens) do
      parse_arguments_rest(rest, [first])
    end
  end

  defp parse_arguments_rest([{:comma, _, _, _} | rest], acc) do
    with {:ok, arg, rest} <- parse_expression_or_named_arg(rest) do
      parse_arguments_rest(rest, [arg | acc])
    end
  end

  defp parse_arguments_rest(tokens, acc) do
    {:ok, Enum.reverse(acc), tokens}
  end

  # Support named arguments like `threshold: 0.75`
  defp parse_expression_or_named_arg([{:identifier, name, _, _}, {:colon, _, _, _} | rest]) do
    with {:ok, value, rest} <- parse_expression(rest) do
      {:ok, {:named_arg, name, value}, rest}
    end
  end

  defp parse_expression_or_named_arg(tokens) do
    parse_expression(tokens)
  end

  # Action ::= SimpleAction | CompoundAction
  defp parse_action([{:execute, _, _, _} | rest]) do
    parse_execute_action(rest)
  end

  defp parse_action([{:report, _, _, _} | rest]) do
    parse_report_action(rest)
  end

  defp parse_action([{:reject, _, _, _} | rest]) do
    parse_reject_action(rest)
  end

  defp parse_action([{:accept, _, _, _} | rest]) do
    parse_accept_action(rest)
  end

  defp parse_action([{:begin, _, _, _} | rest]) do
    parse_block_action(rest, [])
  end

  defp parse_action([{:if, _, _, _} | rest]) do
    parse_conditional_action(rest)
  end

  defp parse_action([token | _]) do
    Errors.error(:action, [:execute, :report, :reject, :accept, :begin, :if], token,
      suggestion: "Actions must be one of: EXECUTE(...), REPORT(...), REJECT(), ACCEPT(), BEGIN...END, or IF...THEN...")
  end

  # EXECUTE(function, args...)
  defp parse_execute_action(tokens) do
    with {:ok, tokens} <- expect(:lparen, tokens),
         {:ok, name, rest} <- expect_identifier(tokens) do
      case rest do
        [{:comma, _, _, _} | rest] ->
          with {:ok, args, rest} <- parse_arguments(rest),
               {:ok, rest} <- expect(:rparen, rest) do
            {:ok, AST.execute(name, args), rest}
          end

        _ ->
          with {:ok, rest} <- expect(:rparen, rest) do
            {:ok, AST.execute(name, []), rest}
          end
      end
    end
  end

  # REPORT(message)
  defp parse_report_action(tokens) do
    with {:ok, tokens} <- expect(:lparen, tokens),
         {:ok, expr, rest} <- parse_expression(tokens),
         {:ok, rest} <- expect(:rparen, rest) do
      {:ok, AST.report(expr), rest}
    end
  end

  # REJECT([reason])
  defp parse_reject_action([{:lparen, _, _, _} | rest]) do
    case rest do
      [{:rparen, _, _, _} | rest] ->
        {:ok, AST.reject(nil), rest}

      _ ->
        with {:ok, expr, rest} <- parse_expression(rest),
             {:ok, rest} <- expect(:rparen, rest) do
          {:ok, AST.reject(expr), rest}
        end
    end
  end

  defp parse_reject_action(tokens) do
    {:ok, AST.reject(nil), tokens}
  end

  # ACCEPT([reason])
  defp parse_accept_action([{:lparen, _, _, _} | rest]) do
    case rest do
      [{:rparen, _, _, _} | rest] ->
        {:ok, AST.accept(nil), rest}

      _ ->
        with {:ok, expr, rest} <- parse_expression(rest),
             {:ok, rest} <- expect(:rparen, rest) do
          {:ok, AST.accept(expr), rest}
        end
    end
  end

  defp parse_accept_action(tokens) do
    {:ok, AST.accept(nil), tokens}
  end

  # BEGIN { Action } END
  defp parse_block_action([{:end_block, _, _, _} | rest], acc) do
    {:ok, AST.block(Enum.reverse(acc)), rest}
  end

  defp parse_block_action(tokens, acc) do
    with {:ok, action, rest} <- parse_action(tokens) do
      parse_block_action(rest, [action | acc])
    end
  end

  # IF Condition THEN Action [ ELSE Action ]
  defp parse_conditional_action(tokens) do
    with {:ok, condition, rest} <- parse_logical_expr(tokens),
         {:ok, rest} <- expect(:then, rest),
         {:ok, then_action, rest} <- parse_action(rest) do
      case rest do
        [{:else, _, _, _} | rest] ->
          with {:ok, else_action, rest} <- parse_action(rest) do
            {:ok, AST.conditional(condition, then_action, else_action), rest}
          end

        _ ->
          {:ok, AST.conditional(condition, then_action, nil), rest}
      end
    end
  end

  # Helpers

  defp expect(expected_type, [{actual_type, _, _, _} | rest]) when expected_type == actual_type do
    {:ok, rest}
  end

  defp expect(expected_type, [token | _] = _tokens) do
    Errors.error(:expression, expected_type, token)
  end

  defp expect(expected_type, []) do
    Errors.error(:expression, expected_type, nil)
  end

  defp expect_identifier([{:identifier, name, _, _} | rest]) do
    {:ok, name, rest}
  end

  defp expect_identifier([token | _] = _tokens) do
    Errors.error(:expression, "an identifier", token)
  end

  defp expect_identifier([]) do
    Errors.error(:expression, "an identifier", nil)
  end

  defp expect_integer([{:integer, value, _, _} | rest]) do
    {:ok, value, rest}
  end

  defp expect_integer([{:hex_integer, value, _, _} | rest]) do
    {:ok, value, rest}
  end

  defp expect_integer([{:binary_integer, value, _, _} | rest]) do
    {:ok, value, rest}
  end

  defp expect_integer([{:octal_integer, value, _, _} | rest]) do
    {:ok, value, rest}
  end

  defp expect_integer([token | _] = _tokens) do
    Errors.error(:metadata, "an integer", token)
  end

  defp expect_integer([]) do
    Errors.error(:metadata, "an integer", nil)
  end
end
