# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Consensus.Raft do
  @moduledoc """
  Raft consensus implementation for distributed policy execution.

  This module implements the Raft consensus algorithm (Ongaro & Ousterhout, 2014)
  for achieving consensus on policy actions across multiple Phronesis nodes.

  ## Overview

  Raft divides consensus into three sub-problems:
  1. **Leader Election** - Elect a single leader among nodes
  2. **Log Replication** - Leader replicates log entries to followers
  3. **Safety** - Ensure logs are consistent across all nodes

  ## Node States

  Each node is in one of three states:
  - `:follower` - Passively replicates entries from leader
  - `:candidate` - Actively seeking votes to become leader
  - `:leader` - Handles all client requests, replicates to followers

  ## Usage

      # Start a Raft node
      {:ok, pid} = Phronesis.Consensus.Raft.start_link(
        node_id: "node1",
        peers: ["node2", "node3"],
        election_timeout: {150, 300}
      )

      # Propose an action for consensus
      {:ok, index} = Phronesis.Consensus.Raft.propose(pid, action)

      # Wait for commit
      :ok = Phronesis.Consensus.Raft.await_commit(pid, index)

  ## Configuration

  - `:node_id` - Unique identifier for this node
  - `:peers` - List of peer node identifiers
  - `:election_timeout` - {min_ms, max_ms} for election timeout
  - `:heartbeat_interval` - Milliseconds between heartbeats
  """

  use GenServer
  require Logger

  alias Phronesis.Consensus.Raft.{Log, RPC}

  @type node_id :: String.t()
  @type raft_term :: non_neg_integer()
  @type index :: non_neg_integer()
  @type state_name :: :follower | :candidate | :leader

  @type log_entry :: %{
          term: raft_term(),
          index: index(),
          command: any()
        }

  defstruct [
    :node_id,
    :peers,
    :state,
    :current_term,
    :voted_for,
    :log,
    :commit_index,
    :last_applied,
    :leader_id,
    # Leader state
    :next_index,
    :match_index,
    # Timers
    :election_timer,
    :heartbeat_timer,
    # Config
    :election_timeout,
    :heartbeat_interval,
    # Callbacks
    :apply_callback,
    # Pending requests
    :pending_proposals
  ]

  @default_election_timeout {150, 300}
  @default_heartbeat_interval 50

  # Client API

  def start_link(opts) do
    GenServer.start_link(__MODULE__, opts, name: via_tuple(opts[:node_id]))
  end

  @doc """
  Propose a command for consensus.

  Returns `{:ok, index}` if the proposal was accepted (node is leader),
  or `{:error, :not_leader, leader_id}` if this node is not the leader.
  """
  @spec propose(pid() | node_id(), any()) :: {:ok, index()} | {:error, :not_leader, node_id() | nil}
  def propose(server, command) do
    GenServer.call(server, {:propose, command})
  end

  @doc """
  Wait for a log entry to be committed.
  """
  @spec await_commit(pid() | node_id(), index(), timeout()) :: :ok | {:error, :timeout}
  def await_commit(server, index, timeout \\ 5000) do
    GenServer.call(server, {:await_commit, index}, timeout)
  end

  @doc """
  Get the current state of the node.
  """
  @spec get_state(pid() | node_id()) :: map()
  def get_state(server) do
    GenServer.call(server, :get_state)
  end

  @doc """
  Get the current leader.
  """
  @spec get_leader(pid() | node_id()) :: node_id() | nil
  def get_leader(server) do
    GenServer.call(server, :get_leader)
  end

  # Server Callbacks

  @impl true
  def init(opts) do
    node_id = Keyword.fetch!(opts, :node_id)
    peers = Keyword.get(opts, :peers, [])

    state = %__MODULE__{
      node_id: node_id,
      peers: peers,
      state: :follower,
      current_term: 0,
      voted_for: nil,
      log: Log.new(),
      commit_index: 0,
      last_applied: 0,
      leader_id: nil,
      next_index: %{},
      match_index: %{},
      election_timeout: Keyword.get(opts, :election_timeout, @default_election_timeout),
      heartbeat_interval: Keyword.get(opts, :heartbeat_interval, @default_heartbeat_interval),
      apply_callback: Keyword.get(opts, :apply_callback, &default_apply/1),
      pending_proposals: %{}
    }

    # Start election timer
    state = reset_election_timer(state)

    Logger.info("[Raft #{node_id}] Started as follower")

    {:ok, state}
  end

  @impl true
  def handle_call({:propose, command}, from, %{state: :leader} = state) do
    # Append to log
    entry = %{
      term: state.current_term,
      index: Log.last_index(state.log) + 1,
      command: command
    }

    log = Log.append(state.log, entry)

    # Track pending proposal
    pending = Map.put(state.pending_proposals, entry.index, from)

    state = %{state | log: log, pending_proposals: pending}

    # Replicate to followers
    state = replicate_to_followers(state)

    {:noreply, state}
  end

  def handle_call({:propose, _command}, _from, state) do
    {:reply, {:error, :not_leader, state.leader_id}, state}
  end

  def handle_call({:await_commit, index}, from, state) do
    if index <= state.commit_index do
      {:reply, :ok, state}
    else
      # Add to pending
      pending = Map.put(state.pending_proposals, {:await, index}, from)
      {:noreply, %{state | pending_proposals: pending}}
    end
  end

  def handle_call(:get_state, _from, state) do
    info = %{
      node_id: state.node_id,
      state: state.state,
      term: state.current_term,
      leader: state.leader_id,
      log_length: Log.length(state.log),
      commit_index: state.commit_index,
      last_applied: state.last_applied
    }

    {:reply, info, state}
  end

  def handle_call(:get_leader, _from, state) do
    {:reply, state.leader_id, state}
  end

  # RPC Handlers

  @impl true
  def handle_cast({:request_vote, from_node, request}, state) do
    state = handle_request_vote(request, from_node, state)
    {:noreply, state}
  end

  def handle_cast({:request_vote_response, from_node, response}, state) do
    state = handle_vote_response(response, from_node, state)
    {:noreply, state}
  end

  def handle_cast({:append_entries, from_node, request}, state) do
    state = handle_append_entries(request, from_node, state)
    {:noreply, state}
  end

  def handle_cast({:append_entries_response, from_node, response}, state) do
    state = handle_append_entries_response(response, from_node, state)
    {:noreply, state}
  end

  # Timer Handlers

  @impl true
  def handle_info(:election_timeout, %{state: :leader} = state) do
    # Leaders don't have election timeouts
    {:noreply, state}
  end

  def handle_info(:election_timeout, state) do
    Logger.debug("[Raft #{state.node_id}] Election timeout, starting election")
    state = start_election(state)
    {:noreply, state}
  end

  def handle_info(:heartbeat, %{state: :leader} = state) do
    state = send_heartbeats(state)
    state = schedule_heartbeat(state)
    {:noreply, state}
  end

  def handle_info(:heartbeat, state) do
    # Not leader, ignore
    {:noreply, state}
  end

  # Election Logic

  defp start_election(state) do
    new_term = state.current_term + 1

    Logger.info("[Raft #{state.node_id}] Starting election for term #{new_term}")

    state = %{state |
      state: :candidate,
      current_term: new_term,
      voted_for: state.node_id,
      leader_id: nil
    }

    # Vote for self
    votes_received = MapSet.new([state.node_id])

    # Request votes from peers
    request = %{
      term: new_term,
      candidate_id: state.node_id,
      last_log_index: Log.last_index(state.log),
      last_log_term: Log.last_term(state.log)
    }

    for peer <- state.peers do
      RPC.send_request_vote(peer, state.node_id, request)
    end

    # Check if we already have majority (single node cluster)
    state = check_election_won(state, votes_received)

    reset_election_timer(state)
  end

  defp handle_request_vote(request, from_node, state) do
    state =
      if request.term > state.current_term do
        become_follower(state, request.term)
      else
        state
      end

    vote_granted =
      request.term >= state.current_term &&
        (state.voted_for == nil || state.voted_for == request.candidate_id) &&
        log_up_to_date?(request, state)

    state =
      if vote_granted do
        Logger.debug("[Raft #{state.node_id}] Granting vote to #{request.candidate_id}")
        %{state | voted_for: request.candidate_id}
      else
        state
      end

    response = %{term: state.current_term, vote_granted: vote_granted}
    RPC.send_request_vote_response(from_node, state.node_id, response)

    if vote_granted do
      reset_election_timer(state)
    else
      state
    end
  end

  defp handle_vote_response(response, from_node, %{state: :candidate} = state) do
    state =
      if response.term > state.current_term do
        become_follower(state, response.term)
      else
        state
      end

    if state.state == :candidate && response.vote_granted do
      votes_received = MapSet.new([state.node_id, from_node])
      check_election_won(state, votes_received)
    else
      state
    end
  end

  defp handle_vote_response(response, _from_node, state) do
    if response.term > state.current_term do
      become_follower(state, response.term)
    else
      state
    end
  end

  defp check_election_won(state, votes_received) do
    total_nodes = length(state.peers) + 1
    votes_needed = div(total_nodes, 2) + 1

    if MapSet.size(votes_received) >= votes_needed do
      become_leader(state)
    else
      state
    end
  end

  defp log_up_to_date?(request, state) do
    my_last_term = Log.last_term(state.log)
    my_last_index = Log.last_index(state.log)

    request.last_log_term > my_last_term ||
      (request.last_log_term == my_last_term && request.last_log_index >= my_last_index)
  end

  # Leader Logic

  defp become_leader(state) do
    Logger.info("[Raft #{state.node_id}] Became leader for term #{state.current_term}")

    # Initialize leader state
    next_index =
      Map.new(state.peers, fn peer ->
        {peer, Log.last_index(state.log) + 1}
      end)

    match_index = Map.new(state.peers, fn peer -> {peer, 0} end)

    state = %{state |
      state: :leader,
      leader_id: state.node_id,
      next_index: next_index,
      match_index: match_index
    }

    # Cancel election timer
    if state.election_timer do
      Process.cancel_timer(state.election_timer)
    end

    # Send initial heartbeats
    state = send_heartbeats(state)
    schedule_heartbeat(state)
  end

  defp send_heartbeats(state) do
    for peer <- state.peers do
      send_append_entries(state, peer)
    end

    state
  end

  defp send_append_entries(state, peer) do
    next_idx = Map.get(state.next_index, peer, 1)
    prev_log_index = next_idx - 1
    prev_log_term = Log.term_at(state.log, prev_log_index)
    entries = Log.entries_from(state.log, next_idx)

    request = %{
      term: state.current_term,
      leader_id: state.node_id,
      prev_log_index: prev_log_index,
      prev_log_term: prev_log_term,
      entries: entries,
      leader_commit: state.commit_index
    }

    RPC.send_append_entries(peer, state.node_id, request)
  end

  defp replicate_to_followers(state) do
    for peer <- state.peers do
      send_append_entries(state, peer)
    end

    state
  end

  defp handle_append_entries(request, from_node, state) do
    state =
      if request.term > state.current_term do
        become_follower(state, request.term)
      else
        state
      end

    success =
      request.term >= state.current_term &&
        log_matches?(state, request.prev_log_index, request.prev_log_term)

    state =
      if success do
        state = %{state | leader_id: request.leader_id}

        # Append new entries
        log = Log.append_entries(state.log, request.prev_log_index, request.entries)

        # Update commit index
        commit_index =
          if request.leader_commit > state.commit_index do
            min(request.leader_commit, Log.last_index(log))
          else
            state.commit_index
          end

        state = %{state | log: log, commit_index: commit_index}

        # Apply committed entries
        apply_committed_entries(state)
      else
        state
      end

    response = %{
      term: state.current_term,
      success: success,
      match_index: if(success, do: Log.last_index(state.log), else: 0)
    }

    RPC.send_append_entries_response(from_node, state.node_id, response)

    reset_election_timer(state)
  end

  defp handle_append_entries_response(response, from_node, %{state: :leader} = state) do
    state =
      if response.term > state.current_term do
        become_follower(state, response.term)
      else
        state
      end

    if state.state == :leader do
      if response.success do
        # Update next_index and match_index
        next_index = Map.put(state.next_index, from_node, response.match_index + 1)
        match_index = Map.put(state.match_index, from_node, response.match_index)

        state = %{state | next_index: next_index, match_index: match_index}

        # Try to advance commit index
        advance_commit_index(state)
      else
        # Decrement next_index and retry
        next_idx = max(1, Map.get(state.next_index, from_node, 1) - 1)
        next_index = Map.put(state.next_index, from_node, next_idx)
        state = %{state | next_index: next_index}

        # Retry append entries
        send_append_entries(state, from_node)
        state
      end
    else
      state
    end
  end

  defp handle_append_entries_response(response, _from_node, state) do
    if response.term > state.current_term do
      become_follower(state, response.term)
    else
      state
    end
  end

  defp log_matches?(state, prev_log_index, prev_log_term) do
    prev_log_index == 0 ||
      Log.term_at(state.log, prev_log_index) == prev_log_term
  end

  defp advance_commit_index(state) do
    # Find the highest index replicated on majority
    all_match = [Log.last_index(state.log) | Map.values(state.match_index)]

    sorted = Enum.sort(all_match, :desc)
    majority_index = div(length(sorted), 2)
    new_commit = Enum.at(sorted, majority_index, 0)

    if new_commit > state.commit_index &&
         Log.term_at(state.log, new_commit) == state.current_term do
      state = %{state | commit_index: new_commit}
      apply_committed_entries(state)
    else
      state
    end
  end

  defp apply_committed_entries(state) do
    if state.last_applied < state.commit_index do
      entries_to_apply =
        (state.last_applied + 1)..state.commit_index
        |> Enum.map(&Log.entry_at(state.log, &1))
        |> Enum.reject(&is_nil/1)

      for entry <- entries_to_apply do
        state.apply_callback.(entry.command)
      end

      # Notify pending proposals
      pending =
        Enum.reduce(state.commit_index..state.last_applied, state.pending_proposals, fn idx, acc ->
          case Map.pop(acc, idx) do
            {nil, acc} -> acc
            {from, acc} ->
              GenServer.reply(from, {:ok, idx})
              acc
          end
        end)

      %{state | last_applied: state.commit_index, pending_proposals: pending}
    else
      state
    end
  end

  # State Transitions

  defp become_follower(state, new_term) do
    Logger.debug("[Raft #{state.node_id}] Becoming follower for term #{new_term}")

    if state.heartbeat_timer do
      Process.cancel_timer(state.heartbeat_timer)
    end

    state = %{state |
      state: :follower,
      current_term: new_term,
      voted_for: nil,
      leader_id: nil,
      heartbeat_timer: nil
    }

    reset_election_timer(state)
  end

  # Timer Management

  defp reset_election_timer(state) do
    if state.election_timer do
      Process.cancel_timer(state.election_timer)
    end

    {min_timeout, max_timeout} = state.election_timeout
    timeout = min_timeout + :rand.uniform(max_timeout - min_timeout)

    timer = Process.send_after(self(), :election_timeout, timeout)
    %{state | election_timer: timer}
  end

  defp schedule_heartbeat(state) do
    timer = Process.send_after(self(), :heartbeat, state.heartbeat_interval)
    %{state | heartbeat_timer: timer}
  end

  # Helpers

  defp via_tuple(node_id) do
    {:via, Registry, {Phronesis.Consensus.Registry, node_id}}
  end

  defp default_apply(command) do
    Logger.info("[Raft] Applied command: #{inspect(command)}")
    :ok
  end
end
