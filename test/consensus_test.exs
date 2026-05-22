# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.ConsensusTest do
  use ExUnit.Case, async: false
  alias Phronesis.Consensus.Server

  describe "Consensus.Server" do
    setup do
      # Ensure Ra is started
      case Application.ensure_all_started(:ra) do
        {:ok, _} -> :ok
        {:error, _} -> :ok
      end

      # Set up data directory for test
      data_dir = "test/tmp/consensus_test_#{:rand.uniform(10000)}"
      File.mkdir_p!(data_dir)

      on_exit(fn ->
        # Stop any running servers
        try do
          :ra.delete_cluster([{:test_node1, node()}, {:test_vote, node()}, {:test_log, node()}, {:test_status, node()}])
        catch
          _, _ -> :ok
        end

        File.rm_rf!(data_dir)
      end)

      {:ok, data_dir: data_dir}
    end

    @tag :skip
    test "starts a consensus server node", %{data_dir: data_dir} do
      {:ok, pid} = Server.start_link(node_id: :test_node1, data_dir: data_dir)
      assert Process.alive?(pid)

      # Clean up
      GenServer.stop(pid)
    end

    @tag :skip
    test "votes on an action and achieves consensus", %{data_dir: data_dir} do
      {:ok, _pid} = Server.start_link(node_id: :test_vote, data_dir: data_dir)

      # Vote with threshold that should pass (75% approval expected)
      {:ok, consensus_achieved, votes} =
        Server.vote(
          {:accept, "Allow traffic"},
          ["agent1", "agent2", "agent3", "agent4"],
          0.5,
          node_id: :test_vote
        )

      assert is_boolean(consensus_achieved)
      assert is_list(votes)
      assert length(votes) == 4

      # Each vote should be {agent_id, boolean}
      for {agent, vote} <- votes do
        assert is_binary(agent)
        assert is_boolean(vote)
      end
    end

    @tag :skip
    test "records votes in consensus log", %{data_dir: data_dir} do
      {:ok, _pid} = Server.start_link(node_id: :test_log, data_dir: data_dir)

      # Submit first vote
      {:ok, _, _} =
        Server.vote(
          {:accept, "Policy 1"},
          ["agent1", "agent2"],
          0.5,
          node_id: :test_log
        )

      # Submit second vote
      {:ok, _, _} =
        Server.vote(
          {:reject, "Policy 2"},
          ["agent1", "agent2", "agent3"],
          0.67,
          node_id: :test_log
        )

      # Check log
      {:ok, log} = Server.get_log(node_id: :test_log)

      assert is_list(log)
      assert length(log) == 2

      # First entry
      entry1 = Enum.at(log, 0)
      assert entry1.action == {:accept, "Policy 1"}
      assert length(entry1.votes) == 2
      assert entry1.result in [:approved, :rejected]

      # Second entry
      entry2 = Enum.at(log, 1)
      assert entry2.action == {:reject, "Policy 2"}
      assert length(entry2.votes) == 3
    end

    @tag :skip
    test "retrieves cluster status", %{data_dir: data_dir} do
      {:ok, _pid} = Server.start_link(node_id: :test_status, data_dir: data_dir)

      {:ok, status} = Server.status(node_id: :test_status)

      assert is_map(status)
      assert status.node_id == :test_status
      assert status.cluster_name == :phronesis_consensus
      assert is_list(status.members)
    end
  end

  describe "Stdlib.Consensus with mock" do
    test "vote with mock consensus" do
      # Ensure consensus is disabled to use mock
      System.put_env("PHRONESIS_CONSENSUS_ENABLED", "false")

      {:ok, consensus_achieved, votes} =
        Phronesis.Stdlib.Consensus.vote(
          {:accept, "Test action"},
          ["agent1", "agent2", "agent3"],
          0.5
        )

      assert is_boolean(consensus_achieved)
      assert is_list(votes)
      assert length(votes) == 3
    end

    test "count_approvals counts true votes" do
      votes = [
        {"agent1", true},
        {"agent2", false},
        {"agent3", true},
        {"agent4", true}
      ]

      assert Phronesis.Stdlib.Consensus.count_approvals(votes) == 3
    end

    test "count_approvals with no approvals" do
      votes = [
        {"agent1", false},
        {"agent2", false}
      ]

      assert Phronesis.Stdlib.Consensus.count_approvals(votes) == 0
    end

    test "count_approvals with all approvals" do
      votes = [
        {"agent1", true},
        {"agent2", true},
        {"agent3", true}
      ]

      assert Phronesis.Stdlib.Consensus.count_approvals(votes) == 3
    end
  end
end
