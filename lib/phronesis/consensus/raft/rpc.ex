# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Consensus.Raft.RPC do
  @moduledoc """
  RPC transport for Raft consensus.

  Handles communication between Raft nodes, supporting multiple transports:
  - Local (same Erlang node, via Registry)
  - Distributed Erlang (multiple BEAM nodes)
  - TCP (for non-Erlang nodes)

  ## Message Types

  ### RequestVote RPC
  Invoked by candidates to gather votes.

      %{
        term: integer(),
        candidate_id: node_id(),
        last_log_index: integer(),
        last_log_term: integer()
      }

  ### AppendEntries RPC
  Invoked by leader to replicate log entries and send heartbeats.

      %{
        term: integer(),
        leader_id: node_id(),
        prev_log_index: integer(),
        prev_log_term: integer(),
        entries: [entry()],
        leader_commit: integer()
      }
  """

  require Logger

  @type node_id :: String.t()

  @doc """
  Send RequestVote RPC to a peer.
  """
  @spec send_request_vote(node_id(), node_id(), map()) :: :ok
  def send_request_vote(to_node, from_node, request) do
    send_message(to_node, {:request_vote, from_node, request})
  end

  @doc """
  Send RequestVote response.
  """
  @spec send_request_vote_response(node_id(), node_id(), map()) :: :ok
  def send_request_vote_response(to_node, from_node, response) do
    send_message(to_node, {:request_vote_response, from_node, response})
  end

  @doc """
  Send AppendEntries RPC to a peer.
  """
  @spec send_append_entries(node_id(), node_id(), map()) :: :ok
  def send_append_entries(to_node, from_node, request) do
    send_message(to_node, {:append_entries, from_node, request})
  end

  @doc """
  Send AppendEntries response.
  """
  @spec send_append_entries_response(node_id(), node_id(), map()) :: :ok
  def send_append_entries_response(to_node, from_node, response) do
    send_message(to_node, {:append_entries_response, from_node, response})
  end

  # Transport implementations

  defp send_message(to_node, message) do
    case resolve_node(to_node) do
      {:local, pid} ->
        GenServer.cast(pid, message)

      {:remote, node, name} ->
        GenServer.cast({name, node}, message)

      :not_found ->
        Logger.warning("[Raft RPC] Node #{to_node} not found")
        :ok
    end
  end

  defp resolve_node(node_id) do
    # Try local registry first
    case Registry.lookup(Phronesis.Consensus.Registry, node_id) do
      [{pid, _}] ->
        {:local, pid}

      [] ->
        # Try distributed Erlang
        case parse_distributed_node(node_id) do
          {:ok, node, name} ->
            {:remote, node, name}

          :error ->
            :not_found
        end
    end
  end

  defp parse_distributed_node(node_id) do
    case String.split(node_id, "@") do
      [name, host] ->
        node = String.to_atom("#{name}@#{host}")

        if node in [node() | Node.list()] do
          {:ok, node, {:via, Registry, {Phronesis.Consensus.Registry, name}}}
        else
          :error
        end

      _ ->
        :error
    end
  end
end
