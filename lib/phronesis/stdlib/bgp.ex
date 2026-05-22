# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.BGP do
  @moduledoc """
  BGP (Border Gateway Protocol) utility functions for network policy evaluation.

  Provides functions for analyzing BGP routes, AS paths, and route attributes.
  Used by network security and routing policies.

  ## Route Structure

  Routes are represented as maps with these fields:
  - `prefix` - IP prefix (e.g., "192.0.2.0/24")
  - `next_hop` - Next hop IP address
  - `as_path` - List of AS numbers in path (e.g., [64512, 64513, 64514])
  - `origin` - Origin AS number
  - `local_pref` - Local preference value
  - `med` - Multi-exit discriminator

  ## Examples

      route = %{
        prefix: "192.0.2.0/24",
        next_hop: "203.0.113.1",
        as_path: [64512, 64513, 64514],
        origin: 64514,
        local_pref: 100,
        med: 50
      }

      BGP.extract_as_path(route)  #=> [64512, 64513, 64514]
      BGP.get_origin(route)       #=> 64514
      BGP.path_length(route)      #=> 3
  """

  @doc """
  Extract AS path from a BGP route.

  ## Examples

      iex> route = %{as_path: [64512, 64513, 64514]}
      iex> extract_as_path(route)
      [64512, 64513, 64514]
  """
  @spec extract_as_path(map()) :: [non_neg_integer()]
  def extract_as_path(%{as_path: path}) when is_list(path), do: path
  def extract_as_path(_route), do: []

  @doc """
  Get the origin AS number from a route.

  The origin is the last AS in the AS path (the network that originated the route).

  ## Examples

      iex> route = %{as_path: [64512, 64513, 64514]}
      iex> get_origin(route)
      64514
  """
  @spec get_origin(map()) :: non_neg_integer() | nil
  def get_origin(%{origin: origin}), do: origin
  def get_origin(%{as_path: path}) when is_list(path) and length(path) > 0 do
    List.last(path)
  end
  def get_origin(_route), do: nil

  @doc """
  Get the length of the AS path.

  Shorter paths are generally preferred in BGP route selection.

  ## Examples

      iex> route = %{as_path: [64512, 64513, 64514]}
      iex> path_length(route)
      3
  """
  @spec path_length(map()) :: non_neg_integer()
  def path_length(%{as_path: path}) when is_list(path), do: length(path)
  def path_length(_route), do: 0

  @doc """
  Validate a BGP route against common security checks.

  Returns `:valid` if route passes all checks, or `{:invalid, reason}`.

  Checks performed:
  - AS path not empty
  - No private/reserved AS numbers in path
  - Path length within reasonable bounds (< 255)
  - Origin AS is valid

  ## Examples

      iex> route = %{as_path: [1, 2, 3], origin: 3, prefix: "192.0.2.0/24"}
      iex> validate_route(route)
      :valid

      iex> bogon_route = %{as_path: [64512], origin: 64512, prefix: "192.0.2.0/24"}
      iex> validate_route(bogon_route)
      {:invalid, "Private AS number in path: 64512"}
  """
  @spec validate_route(map()) :: :valid | {:invalid, String.t()}
  def validate_route(route) do
    with :ok <- check_as_path_not_empty(route),
         :ok <- check_no_private_asns(route),
         :ok <- check_path_length_reasonable(route),
         :ok <- check_valid_origin(route) do
      :valid
    else
      {:error, reason} -> {:invalid, reason}
    end
  end

  @doc """
  Check if an AS number is a private/reserved ASN.

  Private ASN ranges:
  - 64512-65534 (16-bit private)
  - 4200000000-4294967294 (32-bit private)

  Reserved:
  - 0 (reserved)
  - 23456 (AS_TRANS)
  - 65535 (reserved)
  - 4294967295 (reserved)
  """
  @spec is_private_asn?(non_neg_integer()) :: boolean()
  def is_private_asn?(asn) when asn >= 64512 and asn <= 65534, do: true
  def is_private_asn?(asn) when asn >= 4_200_000_000 and asn <= 4_294_967_294, do: true
  def is_private_asn?(0), do: true
  def is_private_asn?(23456), do: true
  def is_private_asn?(65535), do: true
  def is_private_asn?(4_294_967_295), do: true
  def is_private_asn?(_asn), do: false

  @doc """
  Check if an AS number is in a bogon (invalid/reserved) range.

  Alias for `is_private_asn?/1` - both check for invalid ASNs.
  """
  @spec is_bogon_asn?(non_neg_integer()) :: boolean()
  def is_bogon_asn?(asn), do: is_private_asn?(asn)

  # ============================================================
  # Private Functions - Route Validation
  # ============================================================

  defp check_as_path_not_empty(%{as_path: path}) when is_list(path) and length(path) > 0 do
    :ok
  end
  defp check_as_path_not_empty(_route) do
    {:error, "AS path is empty"}
  end

  defp check_no_private_asns(%{as_path: path}) when is_list(path) do
    case Enum.find(path, &is_private_asn?/1) do
      nil -> :ok
      asn -> {:error, "Private AS number in path: #{asn}"}
    end
  end
  defp check_no_private_asns(_route), do: :ok

  defp check_path_length_reasonable(%{as_path: path}) when is_list(path) do
    if length(path) < 255 do
      :ok
    else
      {:error, "AS path too long: #{length(path)} hops"}
    end
  end
  defp check_path_length_reasonable(_route), do: :ok

  defp check_valid_origin(route) do
    case get_origin(route) do
      nil -> {:error, "No origin AS"}
      origin when is_integer(origin) and origin > 0 -> :ok
      origin -> {:error, "Invalid origin AS: #{inspect(origin)}"}
    end
  end
end
