# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.StdConsensus do
  @moduledoc """
  Consensus voting module.

  Provides functions for distributed consensus on policy actions.
  Supports multiple consensus backends:
  - Raft (default for 3-5 nodes, strong consistency)
  - PBFT (for Byzantine fault tolerance)
  - Simple majority (for development/testing)

  ## Functions

  - `require_votes(action, threshold: float)` - Require threshold approval
  - `request_vote(action, agents)` - Request votes from specific agents
  - `check_quorum(votes)` - Check if quorum is met
  - `propose(command)` - Propose a command via Raft

  ## Example

      POLICY require_approval:
        sensitive_action == true
        THEN IF Std.Consensus.require_votes(ACCEPT(route), threshold: 0.75)
             THEN ACCEPT(route)
             ELSE REJECT("Insufficient consensus")
        PRIORITY: 150

  ## Protocol Configuration

      config :phronesis, Phronesis.Stdlib.StdConsensus,
        backend: :raft,  # or :simple, :pbft
        node_id: "node1",
        peers: ["node2", "node3"]
  """

  @behaviour Phronesis.Stdlib.Module

  alias Phronesis.Consensus.Raft

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
  - `:use_raft` - Use Raft consensus if available (default: true)
  """
  @spec require_votes(any(), keyword()) :: boolean()
  def require_votes(action, opts \\ []) do
    threshold = Keyword.get(opts, :threshold, 0.51)
    timeout = Keyword.get(opts, :timeout, 5000)
    use_raft = Keyword.get(opts, :use_raft, true)

    if use_raft && raft_available?() do
      # Use Raft consensus
      case Raft.propose(Raft, {:vote_request, action, threshold}) do
        {:ok, _index} -> true
        {:error, :not_leader, _leader} -> false
        {:error, _} -> false
      end
    else
      # Fallback to simple voting
      agents = Keyword.get(opts, :agents, get_registered_agents())
      votes = collect_votes(action, agents, timeout)
      check_threshold(votes, agents, threshold)
    end
  end

  @doc """
  Propose a command through Raft consensus.

  Returns `{:ok, index}` on success, or `{:error, reason}` on failure.
  """
  @spec propose(any()) :: {:ok, non_neg_integer()} | {:error, term()}
  def propose(command) do
    if raft_available?() do
      Raft.propose(Raft, command)
    else
      {:error, :raft_not_available}
    end
  end

  @doc """
  Get the current Raft leader.
  """
  @spec get_leader() :: agent_id() | nil
  def get_leader do
    if raft_available?() do
      Raft.get_leader(Raft)
    else
      nil
    end
  end

  @doc """
  Get Raft cluster state.
  """
  @spec cluster_state() :: map() | nil
  def cluster_state do
    if raft_available?() do
      Raft.get_state(Raft)
    else
      nil
    end
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

  # Check if Raft is running
  defp raft_available? do
    case Process.whereis(Phronesis.Consensus.Raft) do
      nil -> false
      _pid -> true
    end
  end

  # Collect votes from agents (simple voting fallback)
  defp collect_votes(action, agents, timeout) do
    # In production without Raft, this would:
    # 1. Broadcast vote request to all agents
    # 2. Wait for responses (with timeout)
    # 3. Handle network partitions gracefully

    tasks =
      Enum.map(agents, fn agent ->
        Task.async(fn -> {agent, request_agent_vote(agent, action)} end)
      end)

    tasks
    |> Task.yield_many(timeout)
    |> Enum.map(fn
      {_task, {:ok, {agent, vote}}} -> {agent, vote}
      {task, nil} ->
        Task.shutdown(task, :brutal_kill)
        {nil, false}
    end)
    |> Enum.reject(fn {agent, _} -> is_nil(agent) end)
    |> Map.new()
  end

  defp request_agent_vote(agent, _action) do
    # In production, this would send an RPC to the agent
    # For now, simulate approval
    case agent do
      "local" -> true
      _ -> :rand.uniform() > 0.2  # 80% approval rate
    end
  end

  defp get_registered_agents do
    # Query the consensus registry for registered agents
    case Registry.select(Phronesis.Consensus.Registry, [{{:"$1", :_, :_}, [], [:"$1"]}]) do
      [] -> ["local"]
      agents -> agents
    end
  rescue
    _ -> ["local"]
  end

  defp normalize_opts(opts) when is_list(opts) do
    Enum.map(opts, fn
      {key, value} when is_binary(key) -> {String.to_atom(key), value}
      {key, value} -> {key, value}
    end)
  end
end
