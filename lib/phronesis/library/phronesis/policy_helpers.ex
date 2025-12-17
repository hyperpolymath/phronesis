# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Library.Phronesis.PolicyHelpers do
  @moduledoc """
  Phronesis-specific policy helper functions.

  These helpers are designed specifically for the Phronesis policy language
  and provide higher-level abstractions for common policy patterns.
  """

  alias Phronesis.Library.Common.{Network, Time}

  # ============================================================
  # Policy Construction Helpers
  # ============================================================

  @doc """
  Create a standard BGP route filter policy.
  """
  @spec route_filter(keyword()) :: map()
  def route_filter(opts \\ []) do
    %{
      type: :route_filter,
      prefix: Keyword.get(opts, :prefix),
      prefix_len_range: Keyword.get(opts, :prefix_len_range),
      as_path_regex: Keyword.get(opts, :as_path_regex),
      communities: Keyword.get(opts, :communities, []),
      action: Keyword.get(opts, :action, :accept)
    }
  end

  @doc """
  Create a rate limiting policy.
  """
  @spec rate_limit(keyword()) :: map()
  def rate_limit(opts \\ []) do
    %{
      type: :rate_limit,
      max_requests: Keyword.get(opts, :max_requests, 100),
      window_ms: Keyword.get(opts, :window_ms, 60_000),
      burst: Keyword.get(opts, :burst, 10),
      action_on_exceed: Keyword.get(opts, :action_on_exceed, :reject)
    }
  end

  @doc """
  Create a time-based policy window.
  """
  @spec time_window(keyword()) :: map()
  def time_window(opts \\ []) do
    schedule = Keyword.get(opts, :schedule, "weekdays 08:00-17:00")

    case Time.parse_schedule(schedule) do
      {:ok, parsed} ->
        %{
          type: :time_window,
          schedule: parsed,
          inside_action: Keyword.get(opts, :inside_action, :accept),
          outside_action: Keyword.get(opts, :outside_action, :reject)
        }

      {:error, _} ->
        raise ArgumentError, "Invalid schedule: #{schedule}"
    end
  end

  # ============================================================
  # Policy Evaluation Helpers
  # ============================================================

  @doc """
  Evaluate if a route matches filter criteria.
  """
  @spec matches_route_filter?(map(), map()) :: boolean()
  def matches_route_filter?(route, filter) do
    prefix_matches = check_prefix_match(route[:prefix], filter[:prefix], filter[:prefix_len_range])
    as_path_matches = check_as_path_match(route[:as_path], filter[:as_path_regex])
    community_matches = check_community_match(route[:communities], filter[:communities])

    prefix_matches and as_path_matches and community_matches
  end

  @doc """
  Check rate limit state.
  """
  @spec check_rate_limit(map(), map()) :: {:ok, :allowed} | {:error, :rate_exceeded}
  def check_rate_limit(state, policy) do
    current_count = Map.get(state, :request_count, 0)
    window_start = Map.get(state, :window_start, 0)
    now = System.system_time(:millisecond)

    # Check if we're in a new window
    if now - window_start > policy.window_ms do
      {:ok, :allowed}
    else
      if current_count < policy.max_requests + policy.burst do
        {:ok, :allowed}
      else
        {:error, :rate_exceeded}
      end
    end
  end

  @doc """
  Check if current time is within policy window.
  """
  @spec in_policy_window?(map()) :: boolean()
  def in_policy_window?(%{type: :time_window, schedule: schedule}) do
    now = DateTime.utc_now()
    Time.matches_schedule?(now, schedule)
  end

  # ============================================================
  # BGP-Specific Helpers
  # ============================================================

  @doc """
  Check if a prefix is a bogon (unroutable).
  """
  @spec bogon_prefix?(String.t()) :: boolean()
  def bogon_prefix?(prefix) do
    bogons = [
      # IPv4 bogons
      "0.0.0.0/8",
      "10.0.0.0/8",
      "100.64.0.0/10",
      "127.0.0.0/8",
      "169.254.0.0/16",
      "172.16.0.0/12",
      "192.0.0.0/24",
      "192.0.2.0/24",
      "192.168.0.0/16",
      "198.18.0.0/15",
      "198.51.100.0/24",
      "203.0.113.0/24",
      "224.0.0.0/4",
      "240.0.0.0/4",
      # IPv6 bogons
      "::/8",
      "100::/64",
      "2001:2::/48",
      "2001:db8::/32",
      "fc00::/7",
      "fe80::/10"
    ]

    Enum.any?(bogons, fn bogon ->
      Network.cidrs_overlap?(prefix, bogon)
    end)
  end

  @doc """
  Check if an AS path indicates a possible route leak.
  """
  @spec possible_route_leak?(list(), keyword()) :: boolean()
  def possible_route_leak?(as_path, opts \\ []) do
    peer_type = Keyword.get(opts, :peer_type, :customer)
    my_asn = Keyword.get(opts, :my_asn)

    case peer_type do
      :customer ->
        # Customer shouldn't announce routes with our ASN or known transit ASNs
        transit_asns = Keyword.get(opts, :transit_asns, [])
        Enum.any?(as_path, &(&1 in [my_asn | transit_asns]))

      :peer ->
        # Peer shouldn't announce routes learned from other peers
        false

      :transit ->
        # Transit routes are generally okay
        false
    end
  end

  @doc """
  Calculate BGP best path preference.
  """
  @spec calculate_preference(map()) :: integer()
  def calculate_preference(route) do
    base = 100

    # Prefer shorter AS paths
    as_path_len = Network.as_path_length(route[:as_path] || [])
    as_path_penalty = as_path_len * 10

    # Prefer higher local_pref
    local_pref_bonus = div(route[:local_pref] || 100, 10)

    # Prefer lower MED
    med_penalty = div(route[:med] || 0, 100)

    base + local_pref_bonus - as_path_penalty - med_penalty
  end

  # ============================================================
  # Firewall Helpers
  # ============================================================

  @doc """
  Match a packet against firewall criteria.
  """
  @spec packet_matches?(map(), map()) :: boolean()
  def packet_matches?(packet, rule) do
    src_matches = match_ip(packet[:src_ip], rule[:src_ip])
    dst_matches = match_ip(packet[:dst_ip], rule[:dst_ip])
    proto_matches = match_protocol(packet[:protocol], rule[:protocol])
    port_matches = match_port(packet[:dst_port], rule[:dst_port])

    src_matches and dst_matches and proto_matches and port_matches
  end

  @doc """
  Check if traffic should be logged.
  """
  @spec should_log?(map(), keyword()) :: boolean()
  def should_log?(packet, opts \\ []) do
    log_level = Keyword.get(opts, :log_level, :none)
    action = Keyword.get(opts, :action, :accept)

    case log_level do
      :all -> true
      :denied -> action == :reject or action == :drop
      :established -> packet[:flags] == :established
      :none -> false
      _ -> false
    end
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  defp check_prefix_match(_, nil, _), do: true

  defp check_prefix_match(route_prefix, filter_prefix, len_range) do
    base_match = Network.cidrs_overlap?(route_prefix, filter_prefix)

    len_match = case len_range do
      nil -> true
      {min, max} ->
        case Network.parse_cidr(route_prefix) do
          {:ok, _, len} -> len >= min and len <= max
          _ -> false
        end
    end

    base_match and len_match
  end

  defp check_as_path_match(_, nil), do: true

  defp check_as_path_match(as_path, regex) when is_binary(regex) do
    path_str = as_path
      |> Enum.map(&to_string/1)
      |> Enum.join(" ")

    Regex.match?(~r/#{regex}/, path_str)
  end

  defp check_community_match(_, []), do: true
  defp check_community_match(nil, _), do: false

  defp check_community_match(route_communities, filter_communities) do
    Enum.all?(filter_communities, fn required ->
      required in route_communities
    end)
  end

  defp match_ip(_, nil), do: true

  defp match_ip(packet_ip, rule_cidr) do
    Network.ip_in_cidr?(packet_ip, rule_cidr)
  end

  defp match_protocol(_, nil), do: true
  defp match_protocol(_, :any), do: true
  defp match_protocol(proto, proto), do: true
  defp match_protocol(_, _), do: false

  defp match_port(_, nil), do: true

  defp match_port(port, range) when is_tuple(range) do
    Network.port_in_range?(port, range)
  end

  defp match_port(port, port), do: true
  defp match_port(_, _), do: false
end
