# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Consensus.Server.Machine do
  @moduledoc """
  Ra state machine for Phronesis consensus voting.

  Implements the consensus logic as a replicated state machine
  with commands for voting and log management.

  ## State Structure

      %{
        log: [log_entry()],     # Consensus log (append-only)
        votes: %{},             # Current votes by action ID
        agents: MapSet.t()      # Registered agents
      }

  ## Commands

  - `{:vote, action, agents, threshold, timestamp}` - Record a vote
  - `{:register_agent, agent_id}` - Add agent to registry
  - `{:unregister_agent, agent_id}` - Remove agent
  """

  @behaviour :ra_machine

  # ============================================================
  # Ra Machine Callbacks
  # ============================================================

  @impl :ra_machine
  def init(_config) do
    %{
      log: [],
      votes: %{},
      agents: MapSet.new()
    }
  end

  @impl :ra_machine
  def apply(_meta, {:vote, action, agents, threshold, timestamp}, state) do
    # Collect votes from agents (in real impl, this would be distributed)
    votes = collect_votes(action, agents, state)

    # Calculate consensus
    total = length(agents)

    approvals =
      Enum.count(votes, fn {_agent, vote} -> vote == true end)

    consensus_achieved =
      if total == 0 do
        true
      else
        approvals / total >= threshold
      end

    # Create log entry
    result = if consensus_achieved, do: :approved, else: :rejected

    entry = %{
      action: action,
      votes: votes,
      result: result,
      threshold: threshold,
      timestamp: timestamp
    }

    # Update state
    new_state = %{state | log: state.log ++ [entry]}

    # Return result and updated state
    {{:ok, consensus_achieved, votes}, new_state}
  end

  @impl :ra_machine
  def apply(_meta, {:register_agent, agent_id}, state) do
    new_agents = MapSet.put(state.agents, agent_id)
    {:ok, %{state | agents: new_agents}}
  end

  @impl :ra_machine
  def apply(_meta, {:unregister_agent, agent_id}, state) do
    new_agents = MapSet.delete(state.agents, agent_id)
    {:ok, %{state | agents: new_agents}}
  end

  @impl :ra_machine
  def apply(_meta, command, state) do
    # Unknown command
    {{:error, {:unknown_command, command}}, state}
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  # Collect votes from agents
  # In production, this would send requests to distributed agents
  # For now, we simulate based on action type
  defp collect_votes(action, agents, _state) do
    Enum.map(agents, fn agent ->
      vote = simulate_agent_vote(agent, action)
      {agent, vote}
    end)
  end

  # Simulate agent voting (production would use distributed RPC)
  defp simulate_agent_vote(_agent, action) do
    # Deterministic voting based on action type
    case action do
      {:accept, _reason} ->
        # 75% approval rate for ACCEPT actions
        :rand.uniform(100) <= 75

      {:reject, _reason} ->
        # 50% approval rate for REJECT actions
        :rand.uniform(100) <= 50

      {:report, _msg} ->
        # Reports always approved
        true

      _ ->
        # Default: 50/50
        :rand.uniform(2) == 1
    end
  end
end
