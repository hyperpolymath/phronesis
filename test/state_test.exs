# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.StateTest do
  use ExUnit.Case

  alias Phronesis.State

  describe "new/1" do
    test "creates state with defaults" do
      state = State.new()

      assert state.policy_table == %{}
      assert state.consensus_log == []
      assert state.environment == %{}
      assert state.agents == ["local"]
      assert state.consensus_threshold == 0.51
    end

    test "accepts custom options" do
      state = State.new(
        agents: ["a", "b", "c"],
        consensus_threshold: 0.75,
        environment: %{"x" => 1}
      )

      assert state.agents == ["a", "b", "c"]
      assert state.consensus_threshold == 0.75
      assert state.environment == %{"x" => 1}
    end
  end

  describe "bind/3 and lookup/2" do
    test "binds and retrieves variables" do
      state = State.new()
      state = State.bind(state, "x", 42)

      assert {:ok, 42} = State.lookup(state, "x")
    end

    test "returns error for unbound variables" do
      state = State.new()
      assert :error = State.lookup(state, "undefined")
    end

    test "overwrites existing bindings" do
      state = State.new()
      state = State.bind(state, "x", 1)
      state = State.bind(state, "x", 2)

      assert {:ok, 2} = State.lookup(state, "x")
    end
  end

  describe "register_policy/2 and get_policy/2" do
    test "registers and retrieves policies" do
      state = State.new()
      policy = {:policy, "test", {:literal, :boolean, true}, {:accept, nil}, %{priority: 1}}
      state = State.register_policy(state, policy)

      assert {:ok, ^policy} = State.get_policy(state, "test")
    end

    test "returns error for unregistered policies" do
      state = State.new()
      assert :error = State.get_policy(state, "nonexistent")
    end
  end

  describe "queue_action/2 and next_pending_action/1" do
    test "queues and dequeues actions in FIFO order" do
      state = State.new()
      state = State.queue_action(state, {:accept, nil})
      state = State.queue_action(state, {:reject, nil})

      assert {:ok, {:accept, nil}, state} = State.next_pending_action(state)
      assert {:ok, {:reject, nil}, state} = State.next_pending_action(state)
      assert :empty = State.next_pending_action(state)
    end
  end

  describe "consensus_approved?/3" do
    test "returns true when threshold is met" do
      votes = %{"a" => true, "b" => true, "c" => false}
      agents = ["a", "b", "c"]

      # 2/3 = 0.667, which is >= 0.51
      assert State.consensus_approved?(votes, agents, 0.51)
    end

    test "returns false when threshold is not met" do
      votes = %{"a" => true, "b" => false, "c" => false}
      agents = ["a", "b", "c"]

      # 1/3 = 0.333, which is < 0.51
      refute State.consensus_approved?(votes, agents, 0.51)
    end

    test "returns true with no agents" do
      assert State.consensus_approved?(%{}, [], 0.51)
    end

    test "handles high thresholds" do
      votes = %{"a" => true, "b" => true, "c" => true, "d" => false}
      agents = ["a", "b", "c", "d"]

      # 3/4 = 0.75
      assert State.consensus_approved?(votes, agents, 0.75)
      refute State.consensus_approved?(votes, agents, 0.80)
    end
  end

  describe "log_action/4" do
    test "adds entry to consensus log" do
      state = State.new()
      action = {:accept, nil}
      votes = %{"local" => true}

      state = State.log_action(state, action, votes, :approved)

      assert [entry] = state.consensus_log
      assert entry.action == action
      assert entry.votes == votes
      assert entry.result == :approved
      assert %DateTime{} = entry.timestamp
    end

    test "prepends entries (most recent first)" do
      state = State.new()

      state = State.log_action(state, {:accept, nil}, %{}, :approved)
      state = State.log_action(state, {:reject, nil}, %{}, :approved)

      [first, second] = state.consensus_log
      assert first.action == {:reject, nil}
      assert second.action == {:accept, nil}
    end
  end

  describe "policies_by_priority/1" do
    test "returns policies sorted by priority descending" do
      state = State.new()

      policy1 = {:policy, "low", true, {:accept, nil}, %{priority: 10, expires: :never, created_by: nil}}
      policy2 = {:policy, "high", true, {:accept, nil}, %{priority: 100, expires: :never, created_by: nil}}
      policy3 = {:policy, "med", true, {:accept, nil}, %{priority: 50, expires: :never, created_by: nil}}

      state = State.register_policy(state, policy1)
      state = State.register_policy(state, policy2)
      state = State.register_policy(state, policy3)

      policies = State.policies_by_priority(state)
      priorities = Enum.map(policies, fn {:policy, _, _, _, %{priority: p}} -> p end)

      assert priorities == [100, 50, 10]
    end
  end
end
