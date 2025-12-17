# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.StdRPKI do
  @moduledoc """
  RPKI (Resource Public Key Infrastructure) validation module.

  Provides functions for validating BGP route origins against the RPKI.
  Supports real validator backends (Routinator, rpki-client) and mock mode.

  ## Functions

  - `validate(route)` - Validate a route against RPKI ROAs
  - `get_roas(prefix)` - Get ROAs for a prefix
  - `check_origin(route)` - Check if origin AS is authorized

  ## Configuration

  Set the validator backend in your config:

      config :phronesis, Phronesis.Stdlib.StdRPKI,
        backend: :routinator,  # or :rpki_client, :mock
        host: "localhost",
        port: 8323

  ## Example

      POLICY rpki_validation:
        Std.RPKI.validate(route) == "invalid"
        THEN REJECT("RPKI validation failed")
        PRIORITY: 200
  """

  @behaviour Phronesis.Stdlib.Module

  alias Phronesis.Stdlib.StdRPKI.Validator

  @type route :: %{
          required(:prefix) => String.t(),
          required(:origin_as) => non_neg_integer(),
          optional(:as_path) => [non_neg_integer()]
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
  - `:use_validator` - Use real validator if available (default: true)
  """
  @spec validate(route(), keyword()) :: String.t()
  def validate(route, opts \\ [])

  def validate(%{prefix: prefix, origin_as: origin_as}, opts) do
    result =
      if Keyword.get(opts, :use_validator, true) && validator_available?() do
        Validator.validate(prefix, origin_as)
      else
        lookup_roa_local(prefix, origin_as)
      end

    case result do
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
  Get all ROAs/VRPs covering a prefix.

  Returns a list of ROA entries with prefix, max_length, and authorized ASN.
  """
  @spec get_roas(String.t()) :: [map()]
  def get_roas(prefix) do
    if validator_available?() do
      Validator.get_vrps(prefix)
    else
      get_roas_local(prefix)
    end
  end

  @doc """
  Check if the origin AS is authorized for the prefix.
  """
  @spec check_origin(route()) :: boolean()
  def check_origin(%{prefix: prefix, origin_as: origin_as}) do
    validate(%{prefix: prefix, origin_as: origin_as}) == "valid"
  end

  @doc """
  Get validator statistics.
  """
  @spec validator_stats() :: map() | nil
  def validator_stats do
    if validator_available?() do
      Validator.stats()
    else
      nil
    end
  end

  @doc """
  Force refresh of RPKI cache.
  """
  @spec refresh_cache() :: :ok | {:error, :validator_not_running}
  def refresh_cache do
    if validator_available?() do
      Validator.refresh()
    else
      {:error, :validator_not_running}
    end
  end

  # Check if validator process is running
  defp validator_available? do
    case Process.whereis(Validator) do
      nil -> false
      _pid -> true
    end
  end

  # Local ROA lookup (fallback when validator not running)
  defp lookup_roa_local(prefix, origin_as) do
    local_roas = get_roas_local(prefix)

    cond do
      Enum.empty?(local_roas) ->
        :not_found

      Enum.any?(local_roas, fn roa ->
        roa.asn == origin_as && prefix_length_valid?(prefix, roa)
      end) ->
        :valid

      true ->
        :invalid
    end
  end

  defp prefix_length_valid?(prefix, roa) do
    [_, len_str] = String.split(prefix, "/")
    prefix_len = String.to_integer(len_str)
    [_, roa_len_str] = String.split(roa.prefix, "/")
    roa_len = String.to_integer(roa_len_str)

    prefix_len >= roa_len && prefix_len <= roa.max_length
  end

  # Local ROA database (mock/test data)
  # In production, this would query a local cache file
  defp get_roas_local(prefix) do
    all_roas()
    |> Enum.filter(fn roa -> prefix_covered?(roa.prefix, prefix) end)
  end

  defp prefix_covered?(roa_prefix, announced_prefix) do
    {roa_ip, roa_len} = parse_prefix(roa_prefix)
    {ann_ip, ann_len} = parse_prefix(announced_prefix)

    roa_len <= ann_len && ip_matches?(roa_ip, roa_len, ann_ip)
  end

  defp ip_matches?(roa_ip, roa_len, ann_ip) do
    mask = bnot((1 <<< (32 - roa_len)) - 1) &&& 0xFFFFFFFF
    (roa_ip &&& mask) == (ann_ip &&& mask)
  end

  defp parse_prefix(prefix) do
    [ip_str, len_str] = String.split(prefix, "/")
    ip = ip_to_integer(ip_str)
    len = String.to_integer(len_str)
    {ip, len}
  end

  defp ip_to_integer(ip_str) do
    ip_str
    |> String.split(".")
    |> Enum.map(&String.to_integer/1)
    |> Enum.reduce(0, fn octet, acc -> acc * 256 + octet end)
  end

  # Default ROA database (for testing without validator)
  defp all_roas do
    [
      # Cloudflare
      %{prefix: "1.0.0.0/24", max_length: 24, asn: 13335},
      %{prefix: "1.1.1.0/24", max_length: 24, asn: 13335},
      # Google
      %{prefix: "8.8.8.0/24", max_length: 24, asn: 15169},
      %{prefix: "8.8.4.0/24", max_length: 24, asn: 15169},
      # Documentation (RFC 5737)
      %{prefix: "192.0.2.0/24", max_length: 24, asn: 64496},
      %{prefix: "198.51.100.0/24", max_length: 24, asn: 64496},
      %{prefix: "203.0.113.0/24", max_length: 24, asn: 64496},
      # Private (RFC 1918) - for testing
      %{prefix: "10.0.0.0/8", max_length: 24, asn: 64512},
      %{prefix: "172.16.0.0/12", max_length: 24, asn: 64512},
      %{prefix: "192.168.0.0/16", max_length: 24, asn: 64512}
    ]
  end
end
