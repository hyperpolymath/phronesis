# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.InvariantPath do
  @moduledoc """
  A *justification path* — the chain of reasoning behind a design decision:

      principle → construct → static_rule → proof_obligation → runtime_behaviour → audit_trace

  Invariant-Path is what the equivalence engine compares across versions. Rather
  than comparing syntax trees or IR, it compares *paths of justification*, so it
  can tell a harmless refactor from a change in the design's ethical/epistemic
  meaning.

  Paths may be partial (not every decision touches every stage). Steps are
  `{stage, label}` pairs and are kept ordered by the canonical stage order.
  """

  alias Phronesis.Reflexion.{Claim, JudgementEvidenceGraph}

  @type stage ::
          :principle | :construct | :static_rule | :proof_obligation | :runtime_behaviour | :audit_trace

  @stages [:principle, :construct, :static_rule, :proof_obligation, :runtime_behaviour, :audit_trace]

  @type step :: {stage(), String.t()}
  @type t :: %__MODULE__{decision_id: String.t() | nil, steps: [step()], meta: map()}

  defstruct decision_id: nil, steps: [], meta: %{}

  @doc "The canonical ordered list of stages."
  @spec stages() :: [stage()]
  def stages, do: @stages

  @doc "Rank of a stage in the canonical order (used for sorting/comparison)."
  @spec stage_rank(stage()) :: non_neg_integer()
  def stage_rank(stage), do: Enum.find_index(@stages, &(&1 == stage)) || length(@stages)

  @doc "Build a path for `decision_id` from explicit steps (filtered + ordered)."
  @spec new(String.t(), [step()], map()) :: t()
  def new(decision_id, steps, meta \\ %{}) do
    %__MODULE__{decision_id: decision_id, steps: normalize_steps(steps), meta: meta}
  end

  @doc """
  Build the combined justification path for `subject` from all of its claims.

  This is what the façade compares across two source versions: a policy that uses
  a `REPORT` action carries an `:audit_trace` step (and `:construct` REPORT-adequacy);
  dropping `REPORT` removes those load-bearing steps, which the equivalence engine
  reads as a weakening.
  """
  @spec from_claims([Claim.t()], String.t()) :: t()
  def from_claims(claims, subject) when is_list(claims) do
    relevant = Enum.filter(claims, &(&1.subject == subject))
    steps = [{:principle, "practical-judgement"}] ++ Enum.flat_map(relevant, &claim_steps/1)
    new(subject, steps, %{subject: subject})
  end

  @doc "Lift a single judgement (and its evidence) from a JEG into a path."
  @spec from_jeg(JudgementEvidenceGraph.t(), String.t()) :: t()
  def from_jeg(%JudgementEvidenceGraph{} = g, judgement_id) do
    judgement = Map.fetch!(g.judgements, judgement_id)
    evidence = JudgementEvidenceGraph.evidence_for(g, judgement_id)

    steps =
      [{:principle, principle_for(judgement)}, {:construct, judgement.label}] ++
        Enum.map(evidence, &evidence_step/1)

    new(judgement_id, steps, %{from: :jeg})
  end

  defp normalize_steps(steps) do
    steps
    |> Enum.filter(fn {stage, _label} -> stage in @stages end)
    |> Enum.sort_by(fn {stage, _label} -> stage_rank(stage) end)
  end

  defp claim_steps(%Claim{kind: :safety_preservation} = c) do
    [{:construct, c.object}, {:audit_trace, "REPORT:" <> Enum.join(c.conditions, ",")}]
  end

  defp claim_steps(%Claim{kind: :obligation_discharge} = c) do
    [{:static_rule, c.object}, {:proof_obligation, Enum.join(c.conditions, ",")}]
  end

  defp claim_steps(%Claim{kind: :evidence_for} = c) do
    [{:runtime_behaviour, c.object}]
  end

  defp claim_steps(%Claim{kind: :provenance}), do: []
  defp claim_steps(_), do: []

  defp principle_for(%{kind: :safety_preservation}), do: "epistemic-safety"
  defp principle_for(%{kind: :obligation_discharge}), do: "practical-judgement"
  defp principle_for(_), do: "design-intent"

  defp evidence_step(%{kind: :map_territory_report, label: label}), do: {:audit_trace, label}
  defp evidence_step(%{kind: :proof_obligation, label: label}), do: {:proof_obligation, label}
  defp evidence_step(%{kind: :failed_proof_obligation, label: label}), do: {:proof_obligation, label}
  defp evidence_step(%{kind: :benchmark_outcome, label: label}), do: {:runtime_behaviour, label}
  defp evidence_step(%{kind: :safety_invariant, label: label}), do: {:static_rule, label}
  defp evidence_step(%{label: label}), do: {:construct, label}
end
