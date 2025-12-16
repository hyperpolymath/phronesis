# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.StdConsensus do
  @moduledoc """
  Consensus voting module.

  Provides functions for distributed consensus on policy actions.
  Implements voting protocols for multi-agent approval.

  ## Functions

  - `require_votes(action, threshold: float)` - Require threshold approval
  - `request_vote(action, agents)` - Request votes from specific agents
  - `check_quorum(votes)` - Check if quorum is met

  ## Example

      POLICY require_approval:
        sensitive_action == true
        THEN IF Std.Consensus.require_votes(ACCEPT(route), threshold: 0.75)
             THEN ACCEPT(route)
             ELSE REJECT("Insufficient consensus")
        PRIORITY: 150

  ## Protocol

  The consensus module can be backed by different protocols:
  - Raft (default for 3-5 nodes)
  - PBFT (for Byzantine fault tolerance)
  - Simple majority (for development)
  """

  @behaviour Phronesis.Stdlib.Module

  @type agent_id :: String.t()
  @type vote :: boolean()
  @type votes :: %{agent_id() => vote()}

  @impl true
  def call(args) do
    case args do
      [action | opts] -> require_votes(action, normalize_opts(opts))
      _ -> {:error, :invalid_args}
    end
  end

  @doc """
  Require a threshold of votes to approve an action.

  Returns `true` if the threshold is met, `false` otherwise.

  ## Options

  - `:threshold` - Required approval percentage (default: 0.51)
  - `:timeout` - Voting timeout in milliseconds (default: 5000)
  - `:agents` - Specific agents to query (default: all registered)
  """
  @spec require_votes(any(), keyword()) :: boolean()
  def require_votes(action, opts \\ []) do
    threshold = Keyword.get(opts, :threshold, 0.51)
    timeout = Keyword.get(opts, :timeout, 5000)
    agents = Keyword.get(opts, :agents, get_registered_agents())

    votes = collect_votes(action, agents, timeout)
    check_threshold(votes, agents, threshold)
  end

  @doc """
  Request votes from specific agents.

  Returns a map of agent_id => vote.
  """
  @spec request_vote(any(), [agent_id()]) :: votes()
  def request_vote(action, agents) do
    collect_votes(action, agents, 5000)
  end

  @doc """
  Check if votes meet a quorum (simple majority).
  """
  @spec check_quorum(votes()) :: boolean()
  def check_quorum(votes) do
    total = map_size(votes)

    if total == 0 do
      false
    else
      approved = votes |> Map.values() |> Enum.count(& &1)
      approved > total / 2
    end
  end

  @doc """
  Check if votes meet a specific threshold.
  """
  @spec check_threshold(votes(), [agent_id()], float()) :: boolean()
  def check_threshold(votes, agents, threshold) do
    total = length(agents)

    if total == 0 do
      true
    else
      approved = votes |> Map.values() |> Enum.count(& &1)
      approved / total >= threshold
    end
  end

  # Private: collect votes from agents

  defp collect_votes(_action, agents, _timeout) do
    # In production, this would:
    # 1. Broadcast vote request to all agents
    # 2. Wait for responses (with timeout)
    # 3. Handle network partitions gracefully
    #
    # For now, simulate local approval
    Map.new(agents, fn agent -> {agent, true} end)
  end

  defp get_registered_agents do
    # In production, query agent registry
    ["local"]
  end

  defp normalize_opts(opts) when is_list(opts) do
    Enum.map(opts, fn
      {key, value} when is_binary(key) -> {String.to_atom(key), value}
      {key, value} -> {key, value}
    end)
  end
end
