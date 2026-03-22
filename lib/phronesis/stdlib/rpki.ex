# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.RPKI do
  @moduledoc """
  RPKI (Resource Public Key Infrastructure) validation functions.

  Provides route origin validation using RPKI ROAs (Route Origin Authorizations).

  ## RPKI Validation States

  - `:valid` - ROA exists and matches prefix/ASN
  - `:invalid` - ROA exists but does not authorize this origin
  - `:not_found` - No ROA found for this prefix

  ## ROA Structure

  ROAs are represented as maps:
  ```elixir
  %{
    prefix: "192.0.2.0/24",
    max_length: 24,
    asn: 64512
  }
  ```

  ## Examples

      route = %{prefix: "192.0.2.0/24", origin: 64512}
      RPKI.validate(route)  #=> :valid

      route = %{prefix: "192.0.2.0/24", origin: 99999}
      RPKI.validate(route)  #=> :invalid
  """

  @doc """
  Validate a route against RPKI ROAs.

  ## Parameters

  - `route` - Map with `:prefix` and `:origin` fields

  ## Returns

  - `:valid` - ROA exists and authorizes this origin
  - `:invalid` - ROA exists but origin unauthorized
  - `:not_found` - No ROA for this prefix

  ## Examples

      iex> route = %{prefix: "192.0.2.0/24", origin: 64512}
      iex> validate(route)
      :valid
  """
  @spec validate(map()) :: :valid | :invalid | :not_found
  def validate(%{prefix: prefix, origin: origin}) do
    case lookup_roa(prefix) do
      nil ->
        :not_found

      roa ->
        if check_origin(origin, roa.asn) and check_prefix_length(prefix, roa.max_length) do
          :valid
        else
          :invalid
        end
    end
  end
  def validate(_route), do: :not_found

  @doc """
  Check if an origin AS is authorized for a prefix.

  ## Examples

      iex> check_origin(64512, 64512)
      true

      iex> check_origin(64513, 64512)
      false
  """
  @spec check_origin(non_neg_integer(), non_neg_integer()) :: boolean()
  def check_origin(origin_asn, roa_asn) when is_integer(origin_asn) and is_integer(roa_asn) do
    origin_asn == roa_asn
  end
  def check_origin(_origin, _roa), do: false

  @doc """
  Get RPKI validation status as a string.

  ## Examples

      iex> validation_status(:valid)
      "valid"

      iex> validation_status(:invalid)
      "invalid"
  """
  @spec validation_status(atom()) :: String.t()
  def validation_status(:valid), do: "valid"
  def validation_status(:invalid), do: "invalid"
  def validation_status(:not_found), do: "not_found"
  def validation_status(other), do: "unknown:#{inspect(other)}"

  # ============================================================
  # Private Functions
  # ============================================================

  # Lookup ROA for a prefix (mock implementation)
  # In production, this would query an RPKI validator (rpki-client, routinator, etc.)
  defp lookup_roa(prefix) do
    # Mock ROA database - in production, query RPKI cache
    mock_roas = %{
      "192.0.2.0/24" => %{prefix: "192.0.2.0/24", max_length: 24, asn: 64512},
      "198.51.100.0/24" => %{prefix: "198.51.100.0/24", max_length: 24, asn: 64513},
      "203.0.113.0/24" => %{prefix: "203.0.113.0/24", max_length: 24, asn: 64514}
    }

    Map.get(mock_roas, prefix)
  end

  # Check if prefix length is within ROA's max_length
  defp check_prefix_length(prefix, max_length) do
    case String.split(prefix, "/") do
      [_addr, length_str] ->
        case Integer.parse(length_str) do
          {length, ""} -> length <= max_length
          _ -> false
        end
      _ -> false
    end
  end
end
