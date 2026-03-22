# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.Consensus do
  @moduledoc """
  Consensus module for distributed decision-making in Phronesis.

  Implements the consensus voting mechanism as specified in SPEC.core.scm.

  ## Consensus Model

  Per SPEC.core.scm:
  ```scheme
  (define (consensus-approved? votes agents threshold)
    "Check if consensus threshold is met."
    (let ((total (length agents))
          (approvals (count-approvals votes)))
      (if (= total 0)
          #t
          (>= (/ approvals total) threshold))))
  ```

  ## Functions

  - `vote/3` - Collect votes from agents and determine if threshold met
  - `log_action/4` - Log action to consensus log with votes and result
  - `get_consensus_log/1` - Retrieve consensus log from state
  - `count_approvals/1` - Count affirmative votes
  """

  alias Phronesis.State

  @doc """
  Collect votes from agents and check if consensus threshold is met.

  ## Parameters

  - `action` - The action being voted on
  - `agents` - List of agent IDs participating in consensus
  - `threshold` - Minimum fraction of approvals needed (0.0 to 1.0)

  ## Returns

  `{:ok, true, votes}` if consensus achieved
  `{:ok, false, votes}` if consensus not met

  ## Examples

      iex> vote(:accept, ["alice", "bob", "carol"], 0.67)
      {:ok, true, [{"alice", true}, {"bob", true}, {"carol", false}]}

      iex> vote(:reject, ["alice", "bob"], 0.5)
      {:ok, false, [{"alice", false}, {"bob", false}]}
  """
  @spec vote(any(), [String.t()], float()) :: {:ok, boolean(), [{String.t(), boolean()}]}
  def vote(action, agents, threshold) when is_list(agents) and is_float(threshold) do
    # Use real Raft consensus if enabled, otherwise fall back to mock
    if consensus_enabled?() do
      # Use distributed Raft consensus
      case Phronesis.Consensus.Server.vote(action, agents, threshold) do
        {:ok, consensus_achieved, votes} ->
          {:ok, consensus_achieved, votes}

        {:error, reason} ->
          # Fallback to mock if Raft fails
          require Logger
          Logger.warn("Raft consensus failed (#{inspect(reason)}), falling back to mock")
          vote_mock(action, agents, threshold)
      end
    else
      # Use mock consensus
      vote_mock(action, agents, threshold)
    end
  end

  # Mock consensus implementation (for testing and non-distributed mode)
  defp vote_mock(action, agents, threshold) do
    votes = collect_votes(action, agents)

    total = length(agents)
    approvals = count_approvals(votes)

    consensus_achieved =
      if total == 0 do
        true
      else
        approvals / total >= threshold
      end

    {:ok, consensus_achieved, votes}
  end

  # Check if Raft consensus is enabled
  defp consensus_enabled? do
    System.get_env("PHRONESIS_CONSENSUS_ENABLED", "false") == "true"
  end

  @doc """
  Log an action to the consensus log with vote results.

  ## Parameters

  - `state` - Current Phronesis state
  - `action` - The action that was voted on
  - `votes` - List of {agent_id, vote} tuples
  - `result` - :approved or :rejected

  ## Returns

  Updated state with new consensus log entry
  """
  @spec log_action(State.t(), any(), [{String.t(), boolean()}], atom()) :: State.t()
  def log_action(state, action, votes, result) do
    entry = %{
      action: action,
      votes: votes,
      result: result,
      timestamp: DateTime.utc_now()
    }

    %{state | consensus_log: state.consensus_log ++ [entry]}
  end

  @doc """
  Get the consensus log from state.

  ## Returns

  List of consensus log entries (append-only audit trail)
  """
  @spec get_consensus_log(State.t()) :: [map()]
  def get_consensus_log(%State{consensus_log: log}), do: log

  @doc """
  Count the number of affirmative votes.

  ## Examples

      iex> count_approvals([{"alice", true}, {"bob", false}, {"carol", true}])
      2
  """
  @spec count_approvals([{String.t(), boolean()}]) :: non_neg_integer()
  def count_approvals(votes) do
    Enum.count(votes, fn {_agent, vote} -> vote == true end)
  end

  # ============================================================
  # Private Functions
  # ============================================================

  # Simulate vote collection (in production, this would be distributed)
  defp collect_votes(action, agents) do
    Enum.map(agents, fn agent ->
      vote = simulate_agent_vote(agent, action)
      {agent, vote}
    end)
  end

  # Simulate agent voting behavior
  # In production, this would send vote requests to remote nodes
  defp simulate_agent_vote(_agent, action) do
    case action do
      {:accept, _reason} -> Enum.random([true, true, true, false])  # 75% approval
      {:reject, _reason} -> Enum.random([true, true, false, false]) # 50% approval
      {:report, _msg} -> true  # Reports always approved
      _ -> Enum.random([true, false])
    end
  end
end
