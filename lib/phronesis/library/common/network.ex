# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Library.Common.Network do
  @moduledoc """
  Common network utilities shared across network policy languages.

  This module provides fundamental network operations that are
  language-agnostic and can be reused by any network policy DSL.
  """

  import Bitwise

  # ============================================================
  # IP Address Operations
  # ============================================================

  @doc """
  Parse an IPv4 address string to a tuple.
  """
  @spec parse_ipv4(String.t()) :: {:ok, :inet.ip4_address()} | {:error, :invalid_ipv4}
  def parse_ipv4(str) when is_binary(str) do
    case :inet.parse_ipv4strict_address(String.to_charlist(str)) do
      {:ok, addr} -> {:ok, addr}
      {:error, _} -> {:error, :invalid_ipv4}
    end
  end

  @doc """
  Parse an IPv6 address string to a tuple.
  """
  @spec parse_ipv6(String.t()) :: {:ok, :inet.ip6_address()} | {:error, :invalid_ipv6}
  def parse_ipv6(str) when is_binary(str) do
    case :inet.parse_ipv6strict_address(String.to_charlist(str)) do
      {:ok, addr} -> {:ok, addr}
      {:error, _} -> {:error, :invalid_ipv6}
    end
  end

  @doc """
  Check if an IP address is within a CIDR block.
  """
  @spec ip_in_cidr?(String.t() | tuple(), String.t()) :: boolean()
  def ip_in_cidr?(ip, cidr) when is_binary(ip) do
    case parse_ip(ip) do
      {:ok, addr} -> ip_in_cidr?(addr, cidr)
      _ -> false
    end
  end

  def ip_in_cidr?(ip_tuple, cidr) when is_tuple(ip_tuple) and is_binary(cidr) do
    case parse_cidr(cidr) do
      {:ok, network, prefix_len} ->
        ip_matches_prefix?(ip_tuple, network, prefix_len)
      _ ->
        false
    end
  end

  @doc """
  Parse a CIDR notation string.
  """
  @spec parse_cidr(String.t()) :: {:ok, tuple(), non_neg_integer()} | {:error, :invalid_cidr}
  def parse_cidr(cidr) when is_binary(cidr) do
    case String.split(cidr, "/") do
      [ip_str, len_str] ->
        with {len, ""} <- Integer.parse(len_str),
             {:ok, ip} <- parse_ip(ip_str),
             true <- valid_prefix_length?(ip, len) do
          {:ok, ip, len}
        else
          _ -> {:error, :invalid_cidr}
        end

      _ ->
        {:error, :invalid_cidr}
    end
  end

  @doc """
  Check if two CIDR blocks overlap.
  """
  @spec cidrs_overlap?(String.t(), String.t()) :: boolean()
  def cidrs_overlap?(cidr1, cidr2) do
    with {:ok, ip1, len1} <- parse_cidr(cidr1),
         {:ok, ip2, len2} <- parse_cidr(cidr2) do
      smaller_len = min(len1, len2)
      mask1 = ip_to_integer(ip1) |> apply_mask(smaller_len, tuple_size(ip1))
      mask2 = ip_to_integer(ip2) |> apply_mask(smaller_len, tuple_size(ip2))
      mask1 == mask2
    else
      _ -> false
    end
  end

  @doc """
  Get the network address for a CIDR.
  """
  @spec network_address(String.t()) :: {:ok, String.t()} | {:error, term()}
  def network_address(cidr) do
    case parse_cidr(cidr) do
      {:ok, ip, len} ->
        masked = apply_mask_tuple(ip, len)
        {:ok, ip_to_string(masked)}
      error ->
        error
    end
  end

  @doc """
  Get the broadcast address for an IPv4 CIDR.
  """
  @spec broadcast_address(String.t()) :: {:ok, String.t()} | {:error, term()}
  def broadcast_address(cidr) do
    case parse_cidr(cidr) do
      {:ok, ip, len} when tuple_size(ip) == 4 ->
        int_ip = ip_to_integer(ip)
        host_bits = 32 - len
        broadcast = bor(apply_mask(int_ip, len, 4), (1 <<< host_bits) - 1)
        {:ok, ip_to_string(integer_to_ip4(broadcast))}
      {:ok, _, _} ->
        {:error, :ipv6_no_broadcast}
      error ->
        error
    end
  end

  # ============================================================
  # AS Path Operations
  # ============================================================

  @doc """
  Parse an AS path string.

  Supports both standard format (e.g., "65001 65002 65003") and
  AS_SET notation (e.g., "65001 {65002 65003}").
  """
  @spec parse_as_path(String.t()) :: {:ok, list()} | {:error, :invalid_as_path}
  def parse_as_path(str) when is_binary(str) do
    try do
      segments = parse_as_segments(str)
      {:ok, segments}
    rescue
      _ -> {:error, :invalid_as_path}
    end
  end

  @doc """
  Check if an AS path contains a specific ASN.
  """
  @spec as_path_contains?(list(), non_neg_integer()) :: boolean()
  def as_path_contains?(path, asn) when is_list(path) and is_integer(asn) do
    Enum.any?(path, fn
      {:as_seq, asns} -> asn in asns
      {:as_set, asns} -> asn in asns
      asn_val when is_integer(asn_val) -> asn_val == asn
    end)
  end

  @doc """
  Get the origin ASN from an AS path.
  """
  @spec origin_asn(list()) :: {:ok, non_neg_integer()} | {:error, :empty_path}
  def origin_asn([]), do: {:error, :empty_path}

  def origin_asn(path) when is_list(path) do
    case List.last(path) do
      {:as_seq, [last | _]} -> {:ok, last}
      {:as_set, _} -> {:error, :ambiguous_origin}
      asn when is_integer(asn) -> {:ok, asn}
      _ -> {:error, :invalid_path}
    end
  end

  @doc """
  Get the AS path length.
  """
  @spec as_path_length(list()) :: non_neg_integer()
  def as_path_length(path) when is_list(path) do
    Enum.reduce(path, 0, fn
      {:as_seq, asns}, acc -> acc + length(asns)
      {:as_set, _}, acc -> acc + 1  # AS_SET counts as 1
      _, acc -> acc + 1
    end)
  end

  # ============================================================
  # Port and Protocol Operations
  # ============================================================

  @doc """
  Check if a port number is valid.
  """
  @spec valid_port?(integer()) :: boolean()
  def valid_port?(port) when is_integer(port), do: port >= 0 and port <= 65535

  @doc """
  Parse a port range string (e.g., "80-443" or "22").
  """
  @spec parse_port_range(String.t()) :: {:ok, {integer(), integer()}} | {:error, :invalid_range}
  def parse_port_range(str) when is_binary(str) do
    case String.split(str, "-") do
      [single] ->
        case Integer.parse(single) do
          {port, ""} when port >= 0 and port <= 65535 -> {:ok, {port, port}}
          _ -> {:error, :invalid_range}
        end

      [from_str, to_str] ->
        with {from, ""} <- Integer.parse(from_str),
             {to, ""} <- Integer.parse(to_str),
             true <- valid_port?(from) and valid_port?(to) and from <= to do
          {:ok, {from, to}}
        else
          _ -> {:error, :invalid_range}
        end

      _ ->
        {:error, :invalid_range}
    end
  end

  @doc """
  Check if a port is within a range.
  """
  @spec port_in_range?(integer(), {integer(), integer()}) :: boolean()
  def port_in_range?(port, {from, to}) do
    port >= from and port <= to
  end

  # ============================================================
  # Community Operations
  # ============================================================

  @doc """
  Parse a BGP community string (standard format: "ASN:value").
  """
  @spec parse_community(String.t()) :: {:ok, {non_neg_integer(), non_neg_integer()}} | {:error, :invalid_community}
  def parse_community(str) when is_binary(str) do
    case String.split(str, ":") do
      [asn_str, val_str] ->
        with {asn, ""} <- Integer.parse(asn_str),
             {val, ""} <- Integer.parse(val_str),
             true <- asn >= 0 and asn <= 65535 and val >= 0 and val <= 65535 do
          {:ok, {asn, val}}
        else
          _ -> {:error, :invalid_community}
        end

      _ ->
        {:error, :invalid_community}
    end
  end

  @doc """
  Format a community tuple as a string.
  """
  @spec format_community({non_neg_integer(), non_neg_integer()}) :: String.t()
  def format_community({asn, val}) do
    "#{asn}:#{val}"
  end

  @doc """
  Well-known communities.
  """
  def well_known_communities do
    %{
      no_export: {65535, 65281},
      no_advertise: {65535, 65282},
      no_export_subconfed: {65535, 65283},
      nopeer: {65535, 65284},
      blackhole: {65535, 666}
    }
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  defp parse_ip(str) do
    case parse_ipv4(str) do
      {:ok, _} = result -> result
      _ -> parse_ipv6(str)
    end
  end

  defp valid_prefix_length?(ip, len) when tuple_size(ip) == 4, do: len >= 0 and len <= 32
  defp valid_prefix_length?(ip, len) when tuple_size(ip) == 8, do: len >= 0 and len <= 128

  defp ip_matches_prefix?(ip, network, prefix_len) when tuple_size(ip) == tuple_size(network) do
    ip_int = ip_to_integer(ip)
    net_int = ip_to_integer(network)
    bits = tuple_size(ip) * (if tuple_size(ip) == 4, do: 8, else: 16)
    mask = mask_for_prefix(prefix_len, bits)
    band(ip_int, mask) == band(net_int, mask)
  end

  defp ip_matches_prefix?(_, _, _), do: false

  defp ip_to_integer({a, b, c, d}) do
    bsl(a, 24) + bsl(b, 16) + bsl(c, 8) + d
  end

  defp ip_to_integer({a, b, c, d, e, f, g, h}) do
    bsl(a, 112) + bsl(b, 96) + bsl(c, 80) + bsl(d, 64) +
    bsl(e, 48) + bsl(f, 32) + bsl(g, 16) + h
  end

  defp integer_to_ip4(int) do
    {band(bsr(int, 24), 0xFF), band(bsr(int, 16), 0xFF),
     band(bsr(int, 8), 0xFF), band(int, 0xFF)}
  end

  defp ip_to_string({a, b, c, d}), do: "#{a}.#{b}.#{c}.#{d}"

  defp ip_to_string({a, b, c, d, e, f, g, h}) do
    [a, b, c, d, e, f, g, h]
    |> Enum.map(&Integer.to_string(&1, 16))
    |> Enum.join(":")
  end

  defp mask_for_prefix(len, bits) do
    bsl(-1, bits - len) |> band((1 <<< bits) - 1)
  end

  defp apply_mask(int, prefix_len, 4), do: band(int, mask_for_prefix(prefix_len, 32))
  defp apply_mask(int, prefix_len, 8), do: band(int, mask_for_prefix(prefix_len, 128))

  defp apply_mask_tuple(ip, prefix_len) when tuple_size(ip) == 4 do
    int = ip_to_integer(ip) |> apply_mask(prefix_len, 4)
    integer_to_ip4(int)
  end

  defp parse_as_segments(str) do
    str
    |> String.trim()
    |> String.split(~r/\s+/)
    |> Enum.map(fn segment ->
      if String.starts_with?(segment, "{") and String.ends_with?(segment, "}") do
        asns = segment
          |> String.slice(1..-2)
          |> String.split(~r/\s+/)
          |> Enum.map(&String.to_integer/1)
        {:as_set, asns}
      else
        String.to_integer(segment)
      end
    end)
  end
end
