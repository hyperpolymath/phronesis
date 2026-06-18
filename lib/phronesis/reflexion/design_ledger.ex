# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.DesignLedger do
  @moduledoc """
  An append-only, hash-chained record of design events.

  The design ledger is deliberately distinct from `Phronesis.Trace`:

    * `Phronesis.Trace` records the *execution* of a single decision at runtime
      (eval / match / vote / action steps).
    * `DesignLedger` records *design* events about the language itself across
      versions (claims, classifications, obligations, notes).

  Entries are never mutated in place; each entry carries the SHA-256 hash of the
  previous entry, giving a tamper-evident chain (satisfying the estate "SHA256+"
  requirement). A ledger entry may *reference* a `Phronesis.Trace` id in its
  payload (an execution trace used as evidence) but never embeds or replaces traces.
  """

  @type kind :: :claim | :classification | :obligation | :note

  @type entry :: %{
          id: String.t(),
          at: DateTime.t(),
          decision_id: String.t(),
          kind: kind(),
          payload: map(),
          prev_hash: String.t() | nil,
          hash: String.t()
        }

  @type t :: %__MODULE__{entries: [entry()]}

  defstruct entries: []

  @doc "An empty ledger."
  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc """
  Append an entry. The new entry's hash chains off the previous entry's hash,
  so the ledger is tamper-evident and strictly append-only.
  """
  @spec append(t(), kind(), map(), keyword()) :: t()
  def append(%__MODULE__{entries: entries} = ledger, kind, payload, opts \\ []) do
    prev_hash =
      case entries do
        [] -> nil
        _ -> List.last(entries).hash
      end

    decision_id = Keyword.get(opts, :decision_id, "—")
    hash = compute_hash(prev_hash, kind, decision_id, payload)

    entry = %{
      id: :crypto.strong_rand_bytes(8) |> Base.encode16(case: :lower),
      at: DateTime.utc_now(),
      decision_id: decision_id,
      kind: kind,
      payload: payload,
      prev_hash: prev_hash,
      hash: hash
    }

    %{ledger | entries: entries ++ [entry]}
  end

  @doc "The entries, oldest first."
  @spec entries(t()) :: [entry()]
  def entries(%__MODULE__{entries: e}), do: e

  @doc "Verify the integrity of the hash chain."
  @spec verify(t()) :: :ok | {:error, String.t()}
  def verify(%__MODULE__{entries: entries}) do
    entries
    |> Enum.reduce_while({:ok, nil}, fn entry, {:ok, prev} ->
      expected = compute_hash(prev, entry.kind, entry.decision_id, entry.payload)

      if expected == entry.hash and entry.prev_hash == prev do
        {:cont, {:ok, entry.hash}}
      else
        {:halt, {:error, "ledger integrity broken at entry #{entry.id}"}}
      end
    end)
    |> case do
      {:ok, _} -> :ok
      {:error, _} = err -> err
    end
  end

  @doc "A JSON-serialisable map."
  @spec to_map(t()) :: map()
  def to_map(%__MODULE__{entries: entries}) do
    %{entries: Enum.map(entries, &Map.update!(&1, :at, fn at -> DateTime.to_iso8601(at) end))}
  end

  defp compute_hash(prev_hash, kind, decision_id, payload) do
    data = "#{prev_hash}|#{kind}|#{decision_id}|#{inspect(payload)}"
    :crypto.hash(:sha256, data) |> Base.encode16(case: :lower)
  end
end
