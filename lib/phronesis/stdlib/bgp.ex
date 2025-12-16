# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.StdBGP do
  @moduledoc """
  BGP (Border Gateway Protocol) utilities module.

  Provides functions for BGP route analysis and path manipulation.

  ## Functions

  - `extract_as_path(route)` - Get the AS path from a route
  - `check_as_path(route)` - Validate AS path (no loops, valid ASNs)
  - `get_origin(route)` - Get the origin AS
  - `path_length(route)` - Get AS path length
  - `any_route_matches(routes, condition)` - Check if any route matches

  ## Example

      POLICY detect_loop:
        my_asn IN Std.BGP.extract_as_path(route)
        THEN REJECT("AS path loop")
        PRIORITY: 300
  """

  @behaviour Phronesis.Stdlib.Module

  @type asn :: non_neg_integer()
  @type route :: %{
          required(:prefix) => String.t(),
          required(:origin_as) => asn(),
          required(:as_path) => [asn()],
          optional(:next_hop) => String.t(),
          optional(:local_pref) => non_neg_integer(),
          optional(:med) => non_neg_integer()
        }

  @impl true
  def call(args) do
    case args do
      [route] -> extract_as_path(route)
      _ -> {:error, :invalid_args}
    end
  end

  @doc """
  Extract the AS path from a route.

  Returns a list of ASNs in the path, from most recent to origin.
  """
  @spec extract_as_path(route()) :: [asn()]
  def extract_as_path(%{as_path: path}) when is_list(path), do: path
  def extract_as_path(_), do: []

  @doc """
  Check if an AS path is valid.

  Validates:
  - No AS loops (same ASN appears twice)
  - All ASNs are valid (> 0, < 2^32)
  - Path is not empty
  """
  @spec check_as_path(route()) :: :ok | {:error, atom()}
  def check_as_path(%{as_path: path}) when is_list(path) do
    cond do
      path == [] -> {:error, :empty_path}
      has_loop?(path) -> {:error, :as_loop}
      not Enum.all?(path, &valid_asn?/1) -> {:error, :invalid_asn}
      true -> :ok
    end
  end

  def check_as_path(_), do: {:error, :missing_path}

  @doc """
  Get the origin AS from a route.

  The origin is the last AS in the path (the one that originated the route).
  """
  @spec get_origin(route()) :: asn() | nil
  def get_origin(%{as_path: []}), do: nil
  def get_origin(%{as_path: path}) when is_list(path), do: List.last(path)
  def get_origin(%{origin_as: origin}), do: origin
  def get_origin(_), do: nil

  @doc """
  Get the AS path length.
  """
  @spec path_length(route()) :: non_neg_integer()
  def path_length(%{as_path: path}) when is_list(path), do: length(path)
  def path_length(_), do: 0

  @doc """
  Check if any route in a set matches a condition.

  This is used for policies that need to check multiple routes.
  """
  @spec any_route_matches([route()], (route() -> boolean())) :: boolean()
  def any_route_matches(routes, condition) when is_list(routes) do
    Enum.any?(routes, condition)
  end

  @doc """
  Check for AS path prepending (same AS repeated at the start).
  """
  @spec prepend_count(route()) :: non_neg_integer()
  def prepend_count(%{as_path: [first | rest]}) do
    Enum.take_while(rest, &(&1 == first)) |> length()
  end

  def prepend_count(_), do: 0

  # Private helpers

  defp has_loop?(path) do
    length(path) != length(Enum.uniq(path))
  end

  defp valid_asn?(asn) when is_integer(asn) and asn > 0 and asn < 4_294_967_296, do: true
  defp valid_asn?(_), do: false
end
