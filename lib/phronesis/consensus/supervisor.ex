# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Consensus.Supervisor do
  @moduledoc """
  Supervisor for Phronesis consensus cluster.

  Manages consensus server nodes and cluster lifecycle.
  """

  use Supervisor
  require Logger

  def start_link(opts) do
    Supervisor.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @impl true
  def init(_opts) do
    # Check if consensus mode is enabled via environment
    consensus_enabled = System.get_env("PHRONESIS_CONSENSUS_ENABLED", "false") == "true"
    node_id = String.to_atom(System.get_env("PHRONESIS_NODE_ID", "node1"))

    children =
      if consensus_enabled do
        Logger.info("Starting consensus server with node_id: #{node_id}")

        [
          {Phronesis.Consensus.Server, [node_id: node_id]}
        ]
      else
        Logger.info("Consensus mode disabled (use PHRONESIS_CONSENSUS_ENABLED=true to enable)")
        []
      end

    Supervisor.init(children, strategy: :one_for_one)
  end
end
