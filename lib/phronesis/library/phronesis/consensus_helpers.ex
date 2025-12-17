# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Library.Phronesis.ConsensusHelpers do
  @moduledoc """
  Phronesis-specific consensus and distributed policy helpers.

  Provides utilities for consensus-gated policy execution, quorum
  calculations, and distributed state management.
  """

  # ============================================================
  # Quorum Calculations
  # ============================================================

  @doc """
  Calculate the quorum requirement for a given number of agents.
  """
  @spec quorum_size(non_neg_integer(), float()) :: non_neg_integer()
  def quorum_size(total_agents, threshold \\ 0.51) do
    ceil(total_agents * threshold)
  end

  @doc """
  Check if quorum is met.
  """
  @spec quorum_met?(non_neg_integer(), non_neg_integer(), float()) :: boolean()
  def quorum_met?(votes, total_agents, threshold \\ 0.51) do
    votes >= quorum_size(total_agents, threshold)
  end

  @doc """
  Calculate Byzantine fault tolerance (BFT) threshold.

  For BFT consensus, we need 2f+1 honest nodes to tolerate f failures.
  """
  @spec bft_threshold(non_neg_integer()) :: non_neg_integer()
  def bft_threshold(total_agents) do
    # Can tolerate (n-1)/3 failures
    max_failures = div(total_agents - 1, 3)
    total_agents - max_failures
  end

  @doc """
  Check if BFT quorum is met.
  """
  @spec bft_quorum_met?(non_neg_integer(), non_neg_integer()) :: boolean()
  def bft_quorum_met?(votes, total_agents) do
    votes >= bft_threshold(total_agents)
  end

  # ============================================================
  # Vote Collection
  # ============================================================

  @doc """
  Tally votes for a proposal.
  """
  @spec tally_votes([{atom(), :approve | :reject | :abstain}]) :: map()
  def tally_votes(votes) do
    Enum.reduce(votes, %{approve: 0, reject: 0, abstain: 0}, fn
      {_agent, :approve}, acc -> %{acc | approve: acc.approve + 1}
      {_agent, :reject}, acc -> %{acc | reject: acc.reject + 1}
      {_agent, :abstain}, acc -> %{acc | abstain: acc.abstain + 1}
      _, acc -> acc
    end)
  end

  @doc """
  Determine proposal outcome from vote tally.
  """
  @spec proposal_outcome(map(), non_neg_integer(), keyword()) :: :approved | :rejected | :pending
  def proposal_outcome(tally, total_agents, opts \\ []) do
    threshold = Keyword.get(opts, :threshold, 0.51)
    require_explicit_reject = Keyword.get(opts, :require_explicit_reject, false)

    approval_quorum = quorum_size(total_agents, threshold)

    cond do
      tally.approve >= approval_quorum ->
        :approved

      require_explicit_reject and tally.reject > total_agents - approval_quorum ->
        :rejected

      not require_explicit_reject and tally.approve + (total_agents - tally.approve - tally.reject - tally.abstain) < approval_quorum ->
        :rejected

      true ->
        :pending
    end
  end

  # ============================================================
  # Policy Versioning
  # ============================================================

  @doc """
  Generate a policy version hash.
  """
  @spec policy_version(map() | binary()) :: binary()
  def policy_version(policy) when is_map(policy) do
    policy
    |> :erlang.term_to_binary()
    |> policy_version()
  end

  def policy_version(policy_binary) when is_binary(policy_binary) do
    :crypto.hash(:sha256, policy_binary)
    |> Base.encode16(case: :lower)
    |> binary_part(0, 16)
  end

  @doc """
  Check if a policy version is newer.
  """
  @spec version_newer?(non_neg_integer(), non_neg_integer()) :: boolean()
  def version_newer?(proposed, current) do
    proposed > current
  end

  @doc """
  Create a versioned policy wrapper.
  """
  @spec versioned_policy(map(), keyword()) :: map()
  def versioned_policy(policy, opts \\ []) do
    %{
      version: Keyword.get(opts, :version, 1),
      hash: policy_version(policy),
      created_at: DateTime.utc_now(),
      author: Keyword.get(opts, :author, "system"),
      policy: policy,
      signatures: Keyword.get(opts, :signatures, [])
    }
  end

  # ============================================================
  # Conflict Resolution
  # ============================================================

  @doc """
  Detect conflicts between policies.
  """
  @spec detect_conflicts([map()]) :: [{map(), map(), atom()}]
  def detect_conflicts(policies) do
    for p1 <- policies,
        p2 <- policies,
        p1 != p2,
        conflict = find_conflict(p1, p2),
        conflict != nil do
      {p1, p2, conflict}
    end
    |> Enum.uniq_by(fn {p1, p2, _} -> {min(p1[:name], p2[:name]), max(p1[:name], p2[:name])} end)
  end

  @doc """
  Resolve policy conflict using priority.
  """
  @spec resolve_conflict(map(), map()) :: map()
  def resolve_conflict(p1, p2) do
    if (p1[:priority] || 100) <= (p2[:priority] || 100) do
      p1
    else
      p2
    end
  end

  @doc """
  Merge non-conflicting policy attributes.
  """
  @spec merge_policies(map(), map()) :: map()
  def merge_policies(p1, p2) do
    Map.merge(p1, p2, fn
      :priority, v1, v2 -> min(v1, v2)
      :conditions, v1, v2 -> merge_conditions(v1, v2)
      :actions, v1, v2 -> v1 ++ v2
      _key, _v1, v2 -> v2
    end)
  end

  # ============================================================
  # State Synchronization
  # ============================================================

  @doc """
  Create a state snapshot for synchronization.
  """
  @spec create_snapshot(map()) :: map()
  def create_snapshot(state) do
    %{
      timestamp: DateTime.utc_now(),
      hash: state_hash(state),
      policies: Map.get(state, :policies, %{}),
      version: Map.get(state, :version, 0)
    }
  end

  @doc """
  Compare state versions.
  """
  @spec state_diverged?(map(), map()) :: boolean()
  def state_diverged?(local, remote) do
    local_hash = state_hash(local)
    remote_hash = state_hash(remote)
    local_hash != remote_hash
  end

  @doc """
  Calculate state hash for comparison.
  """
  @spec state_hash(map()) :: binary()
  def state_hash(state) do
    state
    |> Map.take([:policies, :version])
    |> :erlang.term_to_binary()
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
  end

  @doc """
  Generate sync delta between states.
  """
  @spec sync_delta(map(), map()) :: map()
  def sync_delta(local, remote) do
    local_policies = Map.get(local, :policies, %{})
    remote_policies = Map.get(remote, :policies, %{})

    added = Map.keys(remote_policies) -- Map.keys(local_policies)
    removed = Map.keys(local_policies) -- Map.keys(remote_policies)
    modified = for key <- Map.keys(local_policies),
                   Map.has_key?(remote_policies, key),
                   Map.get(local_policies, key) != Map.get(remote_policies, key),
                   do: key

    %{
      added: Map.take(remote_policies, added),
      removed: removed,
      modified: Map.take(remote_policies, modified)
    }
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  defp find_conflict(p1, p2) do
    cond do
      same_target?(p1, p2) and conflicting_actions?(p1, p2) ->
        :action_conflict

      overlapping_conditions?(p1, p2) and same_priority?(p1, p2) ->
        :priority_conflict

      true ->
        nil
    end
  end

  defp same_target?(p1, p2) do
    p1[:target] == p2[:target]
  end

  defp conflicting_actions?(p1, p2) do
    a1 = p1[:action] || p1[:actions]
    a2 = p2[:action] || p2[:actions]

    (a1 == :accept and a2 == :reject) or
    (a1 == :reject and a2 == :accept)
  end

  defp overlapping_conditions?(p1, p2) do
    # Simplified check - real implementation would analyze conditions
    p1[:condition] == p2[:condition]
  end

  defp same_priority?(p1, p2) do
    (p1[:priority] || 100) == (p2[:priority] || 100)
  end

  defp merge_conditions(c1, c2) when is_list(c1) and is_list(c2) do
    Enum.uniq(c1 ++ c2)
  end

  defp merge_conditions(c1, c2) do
    [c1, c2]
  end
end
