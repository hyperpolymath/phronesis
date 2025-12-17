# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Consensus.Supervisor do
  @moduledoc """
  Supervisor for the Phronesis consensus subsystem.

  Manages the Raft consensus cluster and related processes.

  ## Usage

      # Start the consensus supervisor
      Phronesis.Consensus.Supervisor.start_link(
        node_id: "node1",
        peers: ["node2", "node3"],
        apply_callback: &MyApp.apply_command/1
      )

  ## Configuration

  - `:node_id` - Unique identifier for this node
  - `:peers` - List of peer node identifiers
  - `:apply_callback` - Function to call when entries are committed
  """

  use Supervisor

  def start_link(opts) do
    Supervisor.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @impl true
  def init(opts) do
    children = [
      # Registry for Raft nodes
      {Registry, keys: :unique, name: Phronesis.Consensus.Registry},

      # Raft node
      {Phronesis.Consensus.Raft, opts}
    ]

    Supervisor.init(children, strategy: :one_for_one)
  end

  @doc """
  Start a new Raft node under this supervisor.
  """
  def start_node(opts) do
    spec = {Phronesis.Consensus.Raft, opts}
    Supervisor.start_child(__MODULE__, spec)
  end

  @doc """
  Stop a Raft node.
  """
  def stop_node(node_id) do
    case Registry.lookup(Phronesis.Consensus.Registry, node_id) do
      [{pid, _}] ->
        Supervisor.terminate_child(__MODULE__, pid)

      [] ->
        {:error, :not_found}
    end
  end
end
