# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Consensus.Raft.Log do
  @moduledoc """
  Replicated log for Raft consensus.

  The log is an ordered sequence of entries, each containing:
  - `term` - The term when the entry was created
  - `index` - The position in the log (1-indexed)
  - `command` - The command to apply to the state machine

  ## Log Matching Property

  If two entries in different logs have the same index and term,
  then the logs are identical in all preceding entries.
  """

  @type entry :: %{
          term: non_neg_integer(),
          index: pos_integer(),
          command: any()
        }

  @type t :: %__MODULE__{
          entries: [entry()],
          snapshot_index: non_neg_integer(),
          snapshot_term: non_neg_integer()
        }

  defstruct entries: [], snapshot_index: 0, snapshot_term: 0

  @doc """
  Create a new empty log.
  """
  @spec new() :: t()
  def new do
    %__MODULE__{}
  end

  @doc """
  Get the index of the last entry.
  """
  @spec last_index(t()) :: non_neg_integer()
  def last_index(%__MODULE__{entries: []}), do: 0
  def last_index(%__MODULE__{entries: entries}), do: List.last(entries).index

  @doc """
  Get the term of the last entry.
  """
  @spec last_term(t()) :: non_neg_integer()
  def last_term(%__MODULE__{entries: []}), do: 0
  def last_term(%__MODULE__{entries: entries}), do: List.last(entries).term

  @doc """
  Get the number of entries in the log.
  """
  @spec length(t()) :: non_neg_integer()
  def length(%__MODULE__{entries: entries}), do: Kernel.length(entries)

  @doc """
  Append a single entry to the log.
  """
  @spec append(t(), entry()) :: t()
  def append(%__MODULE__{entries: entries} = log, entry) do
    %{log | entries: entries ++ [entry]}
  end

  @doc """
  Append multiple entries, handling conflicts.

  If an existing entry conflicts with a new one (same index but different term),
  delete the existing entry and all that follow it.
  """
  @spec append_entries(t(), non_neg_integer(), [entry()]) :: t()
  def append_entries(log, _prev_index, []), do: log

  def append_entries(%__MODULE__{entries: entries} = log, prev_index, new_entries) do
    # Truncate log if there's a conflict
    entries = Enum.take_while(entries, fn e -> e.index <= prev_index end)

    # Append new entries
    %{log | entries: entries ++ new_entries}
  end

  @doc """
  Get the entry at a specific index.
  """
  @spec entry_at(t(), pos_integer()) :: entry() | nil
  def entry_at(%__MODULE__{entries: entries}, index) do
    Enum.find(entries, fn e -> e.index == index end)
  end

  @doc """
  Get the term of the entry at a specific index.
  """
  @spec term_at(t(), non_neg_integer()) :: non_neg_integer()
  def term_at(_log, 0), do: 0

  def term_at(%__MODULE__{} = log, index) do
    case entry_at(log, index) do
      nil -> 0
      entry -> entry.term
    end
  end

  @doc """
  Get all entries from a specific index.
  """
  @spec entries_from(t(), pos_integer()) :: [entry()]
  def entries_from(%__MODULE__{entries: entries}, from_index) do
    Enum.filter(entries, fn e -> e.index >= from_index end)
  end

  @doc """
  Get entries in a range (inclusive).
  """
  @spec entries_range(t(), pos_integer(), pos_integer()) :: [entry()]
  def entries_range(%__MODULE__{entries: entries}, from_index, to_index) do
    Enum.filter(entries, fn e ->
      e.index >= from_index && e.index <= to_index
    end)
  end

  @doc """
  Check if the log contains an entry with the given index and term.
  """
  @spec contains?(t(), pos_integer(), non_neg_integer()) :: boolean()
  def contains?(log, index, term) do
    term_at(log, index) == term
  end

  @doc """
  Truncate log to a specific index.
  """
  @spec truncate(t(), non_neg_integer()) :: t()
  def truncate(%__MODULE__{entries: entries} = log, index) do
    %{log | entries: Enum.take_while(entries, fn e -> e.index <= index end)}
  end

  @doc """
  Create a snapshot up to the given index.

  Removes all entries up to and including the snapshot index.
  """
  @spec snapshot(t(), pos_integer(), non_neg_integer()) :: t()
  def snapshot(%__MODULE__{entries: entries} = log, index, term) do
    remaining = Enum.filter(entries, fn e -> e.index > index end)

    %{log |
      entries: remaining,
      snapshot_index: index,
      snapshot_term: term
    }
  end
end
