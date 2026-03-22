# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Diagnostics.Suggestions do
  @moduledoc """
  Suggestion engine for diagnostics.

  Provides "did you mean" suggestions by finding similar names
  using Levenshtein distance and other heuristics.
  """

  @doc """
  Find the most similar name from a list of available names.

  Returns nil if no good match is found.
  """
  def find_similar(name, available_names, opts \\ []) do
    threshold = Keyword.get(opts, :threshold, 3)

    available_names
    |> Enum.map(fn candidate ->
      {candidate, levenshtein_distance(name, candidate)}
    end)
    |> Enum.filter(fn {_candidate, distance} -> distance <= threshold end)
    |> Enum.sort_by(fn {_candidate, distance} -> distance end)
    |> case do
      [] -> nil
      [{candidate, _distance} | _] -> candidate
    end
  end

  @doc """
  Calculate Levenshtein distance between two strings.

  The Levenshtein distance is the minimum number of single-character
  edits (insertions, deletions, or substitutions) required to change
  one string into another.
  """
  def levenshtein_distance(s1, s2) do
    s1 = String.downcase(to_string(s1))
    s2 = String.downcase(to_string(s2))

    s1_length = String.length(s1)
    s2_length = String.length(s2)

    # Initialize matrix
    matrix =
      for i <- 0..s1_length do
        for j <- 0..s2_length do
          cond do
            i == 0 -> j
            j == 0 -> i
            true -> 0
          end
        end
      end

    # Fill matrix
    matrix =
      for i <- 1..s1_length, reduce: matrix do
        matrix ->
          for j <- 1..s2_length, reduce: matrix do
            matrix ->
              char1 = String.at(s1, i - 1)
              char2 = String.at(s2, j - 1)

              cost = if char1 == char2, do: 0, else: 1

              deletion = get_cell(matrix, i - 1, j, s2_length) + 1
              insertion = get_cell(matrix, i, j - 1, s2_length) + 1
              substitution = get_cell(matrix, i - 1, j - 1, s2_length) + cost

              value = Enum.min([deletion, insertion, substitution])
              set_cell(matrix, i, j, s2_length, value)
          end
      end

    get_cell(matrix, s1_length, s2_length, s2_length)
  end

  @doc """
  Find similar variable names from an AST.
  """
  def find_similar_variable(name, ast, opts \\ []) do
    variables = extract_variables(ast)
    find_similar(name, variables, opts)
  end

  @doc """
  Find similar constant names from an AST.
  """
  def find_similar_constant(name, ast, opts \\ []) do
    constants = extract_constants(ast)
    find_similar(name, constants, opts)
  end

  @doc """
  Find similar policy names from an AST.
  """
  def find_similar_policy(name, ast, opts \\ []) do
    policies = extract_policies(ast)
    find_similar(name, policies, opts)
  end

  # Private helper functions

  defp get_cell(matrix, i, j, width) do
    Enum.at(Enum.at(matrix, i), j)
  end

  defp set_cell(matrix, i, j, width, value) do
    List.update_at(matrix, i, fn row ->
      List.update_at(row, j, fn _ -> value end)
    end)
  end

  defp extract_variables(ast) do
    ast
    |> Enum.flat_map(fn node ->
      case node do
        {:policy, _name, condition, _action, _meta} ->
          extract_vars_from_condition(condition)

        _ ->
          []
      end
    end)
    |> Enum.uniq()
  end

  defp extract_vars_from_condition(condition) do
    case condition do
      {:var, name} -> [to_string(name)]
      {:binary_op, _, left, right} -> extract_vars_from_condition(left) ++ extract_vars_from_condition(right)
      {:unary_op, _, operand} -> extract_vars_from_condition(operand)
      {:call, _name, args} -> Enum.flat_map(args, &extract_vars_from_condition/1)
      _ -> []
    end
  end

  defp extract_constants(ast) do
    ast
    |> Enum.filter(&match?({:const, _, _}, &1))
    |> Enum.map(fn {:const, name, _value} -> to_string(name) end)
  end

  defp extract_policies(ast) do
    ast
    |> Enum.filter(&match?({:policy, _, _, _, _}, &1))
    |> Enum.map(fn {:policy, name, _condition, _action, _meta} -> to_string(name) end)
  end
end
