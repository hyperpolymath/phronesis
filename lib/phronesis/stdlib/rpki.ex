# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.StdRPKI do
  @moduledoc """
  RPKI (Resource Public Key Infrastructure) validation module.

  Provides functions for validating BGP route origins against the RPKI.

  ## Functions

  - `validate(route)` - Validate a route against RPKI ROAs
  - `get_roas(prefix)` - Get ROAs for a prefix
  - `check_origin(route)` - Check if origin AS is authorized

  ## Example

      POLICY rpki_validation:
        Std.RPKI.validate(route) == "invalid"
        THEN REJECT("RPKI validation failed")
        PRIORITY: 200
  """

  @behaviour Phronesis.Stdlib.Module

  @type route :: %{
          prefix: String.t(),
          origin_as: non_neg_integer(),
          as_path: [non_neg_integer()]
        }

  @type validation_result :: :valid | :invalid | :not_found

  @impl true
  def call(args) do
    case args do
      [route] -> validate(route)
      [route, opts] when is_list(opts) -> validate(route, opts)
      _ -> {:error, :invalid_args}
    end
  end

  @doc """
  Validate a route against the RPKI.

  Returns:
  - `"valid"` - Route origin is authorized by a ROA
  - `"invalid"` - Route origin is NOT authorized (explicit deny)
  - `"not_found"` - No ROA exists for this prefix

  ## Options

  - `:strict` - Treat "not_found" as invalid (default: false)
  """
  @spec validate(route(), keyword()) :: String.t()
  def validate(route, opts \\ [])

  def validate(%{prefix: prefix, origin_as: origin_as}, opts) do
    # In production, this would query an RPKI validator (e.g., Routinator, rpki-client)
    case lookup_roa(prefix, origin_as) do
      :valid -> "valid"
      :invalid -> "invalid"
      :not_found -> if Keyword.get(opts, :strict, false), do: "invalid", else: "not_found"
    end
  end

  def validate(route, _opts) when is_map(route) do
    # Handle route without expected keys
    "not_found"
  end

  @doc """
  Get all ROAs covering a prefix.

  Returns a list of ROA entries.
  """
  @spec get_roas(String.t()) :: [map()]
  def get_roas(_prefix) do
    # Placeholder - would query RPKI cache
    []
  end

  @doc """
  Check if the origin AS is authorized for the prefix.
  """
  @spec check_origin(route()) :: boolean()
  def check_origin(%{prefix: prefix, origin_as: origin_as}) do
    lookup_roa(prefix, origin_as) == :valid
  end

  # Private: ROA lookup (placeholder)
  defp lookup_roa(_prefix, _origin_as) do
    # In production:
    # 1. Query local RPKI cache (routinator, rpki-client, etc.)
    # 2. Match prefix against ROAs
    # 3. Verify origin AS is in authorized list
    # 4. Check max_length constraint
    :not_found
  end
end
