# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.LSP.Hover do
  @moduledoc """
  Hover documentation for Phronesis LSP.

  Shows documentation when hovering over:
  - Keywords
  - Standard library functions
  - Policy names
  - Variables
  """

  alias Phronesis.LSP.TextDocument

  @doc """
  Compute hover information for a position in a document.
  """
  def compute(document, position) do
    word = TextDocument.word_at_position(document, position)

    case word do
      nil ->
        nil

      word ->
        cond do
          # Standard library function
          String.contains?(word, ".") ->
            stdlib_hover(word)

          # Keyword
          keyword?(word) ->
            keyword_hover(word)

          # Variable or policy name
          true ->
            variable_hover(document, word)
        end
    end
  end

  defp keyword?(word) do
    word in [
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
      "TEST",
      "SCENARIO",
      "GIVEN",
      "EXPECT"
    ]
  end

  defp keyword_hover("POLICY") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## POLICY

        Define a policy with a condition and action.

        **Syntax:**
        ```phronesis
        POLICY policy_name:
          condition
          THEN action
          PRIORITY: number
          EXPIRES: never | timestamp
          CREATED_BY: identifier
        ```

        **Example:**
        ```phronesis
        POLICY rpki_validation:
          Std.RPKI.validate(route) == :invalid
          THEN REJECT("RPKI validation failed")
          PRIORITY: 200
          EXPIRES: never
          CREATED_BY: security_team
        ```
        """
      }
    }
  end

  defp keyword_hover("CONST") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## CONST

        Define a constant value.

        **Syntax:**
        ```phronesis
        CONST name = expression
        ```

        **Example:**
        ```phronesis
        CONST my_asn = 64512
        CONST threshold = 0.67
        ```
        """
      }
    }
  end

  defp keyword_hover("IMPORT") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## IMPORT

        Import a standard library module.

        **Syntax:**
        ```phronesis
        IMPORT module_path
        IMPORT module_path AS alias
        ```

        **Example:**
        ```phronesis
        IMPORT Std.RPKI
        IMPORT Std.BGP
        IMPORT Std.Consensus
        ```
        """
      }
    }
  end

  defp keyword_hover("ACCEPT") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## ACCEPT

        Accept action - allows the situation.

        **Syntax:**
        ```phronesis
        ACCEPT()
        ACCEPT("reason")
        ```

        **Example:**
        ```phronesis
        POLICY allow_owned_as:
          route.origin == my_asn
          THEN ACCEPT("Route from owned AS")
        ```
        """
      }
    }
  end

  defp keyword_hover("REJECT") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## REJECT

        Reject action - denies the situation.

        **Syntax:**
        ```phronesis
        REJECT("reason")
        ```

        **Example:**
        ```phronesis
        POLICY block_bogons:
          Std.BGP.is_bogon_asn(route.origin)
          THEN REJECT("Bogon ASN detected")
        ```
        """
      }
    }
  end

  defp keyword_hover(_keyword) do
    nil
  end

  defp stdlib_hover("Std.RPKI.validate") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## Std.RPKI.validate

        Validate a BGP route against RPKI ROAs (Route Origin Authorizations).

        **Signature:**
        ```phronesis
        Std.RPKI.validate(route) -> :valid | :invalid | :not_found
        ```

        **Parameters:**
        - `route`: Map with `prefix` and `origin` fields

        **Returns:**
        - `:valid` - ROA exists and authorizes this origin
        - `:invalid` - ROA exists but origin unauthorized
        - `:not_found` - No ROA for this prefix

        **Example:**
        ```phronesis
        POLICY rpki_check:
          Std.RPKI.validate(route) == :invalid
          THEN REJECT("RPKI validation failed")
        ```
        """
      }
    }
  end

  defp stdlib_hover("Std.BGP.extract_as_path") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## Std.BGP.extract_as_path

        Extract AS path from a BGP route.

        **Signature:**
        ```phronesis
        Std.BGP.extract_as_path(route) -> [Integer]
        ```

        **Parameters:**
        - `route`: Map with `as_path` field

        **Returns:** List of AS numbers in the path

        **Example:**
        ```phronesis
        CONST path = Std.BGP.extract_as_path(route)
        CONST path_len = Std.BGP.path_length(route)
        ```
        """
      }
    }
  end

  defp stdlib_hover("Std.Consensus.vote") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## Std.Consensus.vote

        Collect votes from agents and check if consensus threshold met.

        **Signature:**
        ```phronesis
        Std.Consensus.vote(action, agents, threshold) -> {Boolean, Votes}
        ```

        **Parameters:**
        - `action`: Action being voted on
        - `agents`: List of agent IDs
        - `threshold`: Minimum fraction needed (0.0 to 1.0)

        **Returns:** `{consensus_achieved, votes}` tuple

        **Example:**
        ```phronesis
        CONST result = Std.Consensus.vote(
          ACCEPT(),
          ["alice", "bob", "carol"],
          0.67
        )
        ```
        """
      }
    }
  end

  defp stdlib_hover("Std.Temporal.now") do
    %{
      "contents" => %{
        "kind" => "markdown",
        "value" => """
        ## Std.Temporal.now

        Get the current UTC timestamp.

        **Signature:**
        ```phronesis
        Std.Temporal.now() -> DateTime
        ```

        **Returns:** Current time as DateTime struct

        **Example:**
        ```phronesis
        CONST current_time = Std.Temporal.now()
        ```
        """
      }
    }
  end

  defp stdlib_hover(_function) do
    # Default hover for unrecognized stdlib functions
    nil
  end

  defp variable_hover(document, var_name) do
    # Try to find variable definition in AST
    case TextDocument.get_ast(document) do
      {:ok, updated_doc} ->
        case find_variable_definition(updated_doc.ast, var_name) do
          {:ok, value} ->
            %{
              "contents" => %{
                "kind" => "markdown",
                "value" => """
                ## #{var_name}

                **Value:** `#{inspect(value)}`
                """
              }
            }

          :not_found ->
            nil
        end

      {:error, _} ->
        nil
    end
  end

  defp find_variable_definition(ast, var_name) when is_list(ast) do
    case Enum.find(ast, fn
           {:const, ^var_name, _value} -> true
           _ -> false
         end) do
      {:const, ^var_name, value} -> {:ok, value}
      _ -> :not_found
    end
  end

  defp find_variable_definition(_, _), do: :not_found
end
