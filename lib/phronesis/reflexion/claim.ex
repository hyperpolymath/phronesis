# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.Claim do
  @moduledoc """
  An explicit, first-class *claim* extracted from a Phronesis design artefact.

  The reflexion layer turns implicit design decisions into explicit claims so the
  language can reason about *why* a design is considered valid. A claim is a small
  subject–predicate–object record with the conditions under which it holds and a
  pointer to the evidence source it was derived from.

  Claim kinds (mirroring the toolchain discussion):

    * `:safety_preservation` — "rule/feature R preserves safety property S under conditions C"
    * `:obligation_discharge` — "feature F exists to discharge obligation O"
    * `:evidence_for`         — "artefact E is evidence for judgement J"
    * `:provenance`           — "symbol/feature originates from source"
  """

  @type kind :: :safety_preservation | :obligation_discharge | :evidence_for | :provenance
  @type source :: {:ast | :compiler | :proof | :benchmark | :human, term()}
  @type confidence :: :asserted | :derived | :stub

  @type t :: %__MODULE__{
          id: String.t(),
          kind: kind(),
          subject: String.t(),
          predicate: String.t(),
          object: String.t(),
          conditions: [String.t()],
          source: source(),
          confidence: confidence(),
          metadata: map()
        }

  defstruct id: nil,
            kind: :provenance,
            subject: "",
            predicate: "",
            object: "",
            conditions: [],
            source: {:ast, nil},
            confidence: :derived,
            metadata: %{}

  @doc """
  Build a claim from a keyword list of fields. An `:id` is generated if absent.
  """
  @spec new(keyword()) :: t()
  def new(fields) when is_list(fields) do
    struct!(__MODULE__, Keyword.put_new_lazy(fields, :id, &generate_id/0))
  end

  @doc "A claim that `subject` preserves safety `property` under `conditions`."
  @spec safety_preservation(String.t(), String.t(), [String.t()], keyword()) :: t()
  def safety_preservation(subject, property, conditions, opts \\ []) do
    new(
      [
        kind: :safety_preservation,
        subject: subject,
        predicate: "preserves",
        object: property,
        conditions: conditions
      ] ++ opts
    )
  end

  @doc "A claim that `feature` exists to discharge `obligation`."
  @spec obligation_discharge(String.t(), String.t(), keyword()) :: t()
  def obligation_discharge(feature, obligation, opts \\ []) do
    new(
      [kind: :obligation_discharge, subject: feature, predicate: "discharges", object: obligation] ++
        opts
    )
  end

  @doc "A claim that `evidence` supports `judgement`."
  @spec evidence_for(String.t(), String.t(), keyword()) :: t()
  def evidence_for(evidence, judgement, opts \\ []) do
    new(
      [kind: :evidence_for, subject: evidence, predicate: "is-evidence-for", object: judgement] ++
        opts
    )
  end

  @doc "A provenance claim: `subject` originates from `origin`."
  @spec provenance(String.t(), String.t(), keyword()) :: t()
  def provenance(subject, origin, opts \\ []) do
    new([kind: :provenance, subject: subject, predicate: "originates-from", object: origin] ++ opts)
  end

  @doc "A JSON-serialisable map (same idiom as `Phronesis.Trace.to_map/1`)."
  @spec to_map(t()) :: map()
  def to_map(%__MODULE__{} = c) do
    %{
      id: c.id,
      kind: c.kind,
      subject: c.subject,
      predicate: c.predicate,
      object: c.object,
      conditions: c.conditions,
      source: source_to_map(c.source),
      confidence: c.confidence,
      metadata: c.metadata
    }
  end

  @doc "Generate a unique claim id (mirrors `Phronesis.Trace`'s id strategy)."
  @spec generate_id() :: String.t()
  def generate_id, do: :crypto.strong_rand_bytes(8) |> Base.encode16(case: :lower)

  defp source_to_map({tag, detail}), do: %{tag: tag, detail: detail_to_string(detail)}

  defp detail_to_string(nil), do: nil
  defp detail_to_string(d) when is_binary(d), do: d
  defp detail_to_string(d) when is_atom(d), do: Atom.to_string(d)
  defp detail_to_string(d), do: inspect(d)
end
