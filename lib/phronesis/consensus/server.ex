# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Consensus.Server do
  @moduledoc """
  Raft-based consensus server for Phronesis distributed policy voting.

  Uses Ra (Erlang Raft implementation) to achieve distributed consensus
  across multiple nodes for policy actions.

  ## Raft Cluster

  The consensus server creates a Raft cluster with:
  - Leader election
  - Log replication
  - Membership changes
  - Snapshot support

  ## State Machine

  The consensus state machine tracks:
  - Policy votes (action, agents, votes, result)
  - Consensus log (append-only audit trail)
  - Agent membership

  ## Usage

      # Start a consensus server node
      {:ok, _} = Phronesis.Consensus.Server.start_link(node_id: :node1)

      # Vote on an action
      {:ok, result, votes} = Phronesis.Consensus.Server.vote(
        {:accept, "Allow traffic"},
        ["agent1", "agent2", "agent3"],
        0.67
      )

      # Query consensus log
      {:ok, log} = Phronesis.Consensus.Server.get_log()
  """

  use GenServer
  require Logger

  @type vote_result :: {:ok, boolean(), [{String.t(), boolean()}]}
  @type log_entry :: %{
          action: any(),
          votes: [{String.t(), boolean()}],
          result: :approved | :rejected,
          timestamp: DateTime.t()
        }

  # Ra cluster configuration
  @cluster_name :phronesis_consensus
  @machine_module __MODULE__.Machine

  # ============================================================
  # Public API
  # ============================================================

  @doc """
  Start a consensus server node.

  ## Options

  - `:node_id` - Unique node identifier (required)
  - `:data_dir` - Directory for Raft data (default: "priv/consensus_data")
  - `:cluster_nodes` - List of other nodes in cluster (default: [])
  """
  def start_link(opts \\ []) do
    node_id = Keyword.get(opts, :node_id, :node1)
    GenServer.start_link(__MODULE__, opts, name: via_tuple(node_id))
  end

  @doc """
  Vote on an action with distributed consensus.

  Submits a vote request to the Raft cluster and waits for consensus.

  ## Parameters

  - `action` - The action to vote on
  - `agents` - List of agent IDs
  - `threshold` - Consensus threshold (0.0 to 1.0)
  - `opts` - Options (`:timeout` in milliseconds, default: 5000)

  ## Returns

  `{:ok, consensus_achieved?, votes}` - Vote result
  `{:error, reason}` - Error (no leader, timeout, etc.)
  """
  @spec vote(any(), [String.t()], float(), keyword()) :: vote_result() | {:error, any()}
  def vote(action, agents, threshold, opts \\ []) do
    timeout = Keyword.get(opts, :timeout, 5000)
    node_id = Keyword.get(opts, :node_id, :node1)

    GenServer.call(via_tuple(node_id), {:vote, action, agents, threshold}, timeout)
  end

  @doc """
  Get the consensus log from the Raft state machine.

  ## Returns

  `{:ok, log}` - List of consensus log entries
  `{:error, reason}` - Error
  """
  @spec get_log(keyword()) :: {:ok, [log_entry()]} | {:error, any()}
  def get_log(opts \\ []) do
    node_id = Keyword.get(opts, :node_id, :node1)
    GenServer.call(via_tuple(node_id), :get_log)
  end

  @doc """
  Get cluster status and membership information.
  """
  @spec status(keyword()) :: {:ok, map()} | {:error, any()}
  def status(opts \\ []) do
    node_id = Keyword.get(opts, :node_id, :node1)
    GenServer.call(via_tuple(node_id), :status)
  end

  @doc """
  Add a new node to the consensus cluster.
  """
  @spec add_member(atom(), keyword()) :: :ok | {:error, any()}
  def add_member(new_node_id, opts \\ []) do
    node_id = Keyword.get(opts, :node_id, :node1)
    GenServer.call(via_tuple(node_id), {:add_member, new_node_id})
  end

  # ============================================================
  # GenServer Callbacks
  # ============================================================

  @impl true
  def init(opts) do
    node_id = Keyword.fetch!(opts, :node_id)
    data_dir = Keyword.get(opts, :data_dir, "priv/consensus_data")
    cluster_nodes = Keyword.get(opts, :cluster_nodes, [])

    # Ensure data directory exists
    File.mkdir_p!(data_dir)

    # Configure Ra cluster
    server_id = {node_id, node()}
    cluster_name = @cluster_name

    # Initial cluster members (self + provided nodes)
    members = [server_id | Enum.map(cluster_nodes, fn n -> {n, node()} end)]

    machine_config = %{
      module: @machine_module,
      init: fn -> %{log: [], votes: %{}} end
    }

    server_config = %{
      id: server_id,
      uid: Atom.to_string(node_id),
      cluster_name: cluster_name,
      log_init_args: %{
        data_dir: Path.join(data_dir, Atom.to_string(node_id))
      },
      initial_members: members,
      machine: machine_config
    }

    # Start Ra server
    case :ra.start_server(server_config) do
      {:ok, _} ->
        Logger.info("Started consensus server: #{inspect(server_id)}")
        {:ok, %{node_id: node_id, server_id: server_id, cluster_name: cluster_name}}

      {:error, {:already_started, _}} ->
        Logger.info("Consensus server already started: #{inspect(server_id)}")
        {:ok, %{node_id: node_id, server_id: server_id, cluster_name: cluster_name}}

      {:error, reason} ->
        Logger.error("Failed to start consensus server: #{inspect(reason)}")
        {:stop, reason}
    end
  end

  @impl true
  def handle_call({:vote, action, agents, threshold}, _from, state) do
    # Submit vote command to Raft cluster
    command = {:vote, action, agents, threshold, DateTime.utc_now()}

    case :ra.process_command(state.server_id, command) do
      {:ok, result, _leader_id} ->
        {:reply, result, state}

      {:timeout, _} ->
        {:reply, {:error, :timeout}, state}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  @impl true
  def handle_call(:get_log, _from, state) do
    # Query Raft state machine
    case :ra.consistent_query(state.server_id, fn s -> {:ok, s.log} end) do
      {:ok, {:ok, log}, _leader_id} ->
        {:reply, {:ok, log}, state}

      {:timeout, _} ->
        {:reply, {:error, :timeout}, state}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  @impl true
  def handle_call(:status, _from, state) do
    case :ra.member_overview(state.server_id) do
      {:ok, overview, _leader_id} ->
        status = %{
          node_id: state.node_id,
          server_id: state.server_id,
          cluster_name: state.cluster_name,
          state: Map.get(overview, :state, :unknown),
          commit_index: Map.get(overview, :commit_index, 0),
          machine_version: Map.get(overview, :machine_version, 0),
          members: Map.get(overview, :membership, [])
        }

        {:reply, {:ok, status}, state}

      {:timeout, _} ->
        {:reply, {:error, :timeout}, state}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  @impl true
  def handle_call({:add_member, new_node_id}, _from, state) do
    new_server_id = {new_node_id, node()}

    case :ra.add_member(state.server_id, new_server_id) do
      {:ok, _, _} ->
        {:reply, :ok, state}

      {:timeout, _} ->
        {:reply, {:error, :timeout}, state}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  defp via_tuple(node_id) do
    {:via, Registry, {Phronesis.Registry, {__MODULE__, node_id}}}
  end
end
