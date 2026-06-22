# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.JudgementEvidenceGraph do
  @moduledoc """
  The language's memory of *why* a design is considered valid.

  Nodes are judgements; each judgement is linked by typed edges to the evidence
  that supports it. The eight evidence kinds mirror the toolchain discussion:
  semantic rationale, safety invariant, benchmark outcome, proof obligation,
  counterexample, map-territory report, human note, and failed proof obligation.

  This is an in-memory graph built from extracted claims (`from_claims/1`); it is
  a first-class artefact of the toolchain, not merely documentation.
  """

  alias Phronesis.Reflexion.Claim

  @type evidence_kind ::
          :semantic_rationale
          | :safety_invariant
          | :benchmark_outcome
          | :proof_obligation
          | :counterexample
          | :map_territory_report
          | :human_note
          | :failed_proof_obligation

  @type judgement :: %{id: String.t(), label: String.t(), claim_id: String.t() | nil, kind: atom()}
  @type evidence :: %{id: String.t(), kind: evidence_kind(), label: String.t()}
  @type edge :: %{from: String.t(), to: String.t(), kind: evidence_kind()}

  @type t :: %__MODULE__{
          judgements: %{optional(String.t()) => judgement()},
          evidence: %{optional(String.t()) => evidence()},
          edges: [edge()],
          meta: map()
        }

  defstruct judgements: %{}, evidence: %{}, edges: [], meta: %{}

  @doc "An empty graph."
  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc "Add a judgement node; returns the updated graph and the node id."
  @spec add_judgement(t(), String.t(), keyword()) :: {t(), String.t()}
  def add_judgement(%__MODULE__{} = g, label, opts \\ []) do
    id = Keyword.get(opts, :id, gen("j"))

    judgement = %{
      id: id,
      label: label,
      claim_id: Keyword.get(opts, :claim_id),
      kind: Keyword.get(opts, :kind, :judgement)
    }

    {%{g | judgements: Map.put(g.judgements, id, judgement)}, id}
  end

  @doc "Attach a typed piece of evidence to a judgement; returns the graph and evidence id."
  @spec add_evidence(t(), String.t(), evidence_kind(), String.t()) :: {t(), String.t()}
  def add_evidence(%__MODULE__{} = g, judgement_id, kind, label) do
    eid = gen("e")
    evidence = %{id: eid, kind: kind, label: label}
    edge = %{from: judgement_id, to: eid, kind: kind}

    {%{g | evidence: Map.put(g.evidence, eid, evidence), edges: g.edges ++ [edge]}, eid}
  end

  @doc "Build a graph from a list of claims (one judgement + one typed evidence edge each)."
  @spec from_claims([Claim.t()]) :: t()
  def from_claims(claims) when is_list(claims) do
    Enum.reduce(claims, new(), fn claim, g ->
      {g, jid} = add_judgement(g, judgement_label(claim), claim_id: claim.id, kind: claim.kind)
      {g, _eid} = add_evidence(g, jid, evidence_kind_for(claim), evidence_label(claim))
      g
    end)
  end

  @doc "The evidence attached to a judgement."
  @spec evidence_for(t(), String.t()) :: [evidence()]
  def evidence_for(%__MODULE__{} = g, judgement_id) do
    g.edges
    |> Enum.filter(&(&1.from == judgement_id))
    |> Enum.map(&Map.fetch!(g.evidence, &1.to))
  end

  @doc "A JSON-serialisable map."
  @spec to_map(t()) :: map()
  def to_map(%__MODULE__{} = g) do
    %{
      judgements: Map.values(g.judgements),
      evidence: Map.values(g.evidence),
      edges: g.edges,
      meta: g.meta
    }
  end

  defp judgement_label(%Claim{} = c), do: "#{c.subject} #{c.predicate} #{c.object}"
  defp evidence_label(%Claim{} = c), do: "claim:#{c.id} (#{c.confidence})"

  # map a claim kind onto the evidence kind that supports its judgement
  defp evidence_kind_for(%Claim{kind: :safety_preservation}), do: :map_territory_report
  defp evidence_kind_for(%Claim{kind: :obligation_discharge}), do: :proof_obligation
  defp evidence_kind_for(%Claim{kind: :evidence_for}), do: :benchmark_outcome
  defp evidence_kind_for(%Claim{kind: :provenance}), do: :semantic_rationale
  defp evidence_kind_for(_), do: :human_note

  defp gen(prefix), do: prefix <> "_" <> (:crypto.strong_rand_bytes(6) |> Base.encode16(case: :lower))
end
