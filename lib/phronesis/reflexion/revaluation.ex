# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.Revaluation do
  @moduledoc """
  The design revaluation loop.

  It consumes an equivalence classification and decides what it means for the
  language: a gate verdict (`:permit` / `:warn` / `:gate`) plus any design
  obligations. Crucially it produces **data only** — it never mutates an AST,
  compiler output, or runtime configuration. Phronesis does not silently change
  its own semantics; it maintains a disciplined account of proposed changes and
  forces risky ones through an explicit obligation.
  """

  alias Phronesis.Reflexion.{DesignObligation, Equivalence}

  @type gate :: :permit | :warn | :gate

  @doc """
  Map a classification delta to a gate verdict and obligations.

    * `:equivalent` / `:refinement` / `:strengthening` → `:permit` (no obligation)
    * `:orthogonal_extension`                          → `:warn` (informational obligation)
    * `:weakening` / `:semantic_drift` / `:contradiction` / `:unresolved` → `:gate` (obligation)
  """
  @spec revaluate(Equivalence.delta(), String.t()) :: {gate(), [DesignObligation.t()]}
  def revaluate(%{classification: classification} = delta, decision_id) do
    case classification do
      :equivalent -> {:permit, []}
      :refinement -> {:permit, []}
      :strengthening -> {:permit, []}
      :orthogonal_extension -> {:warn, [obligation(classification, decision_id, delta)]}
      :weakening -> {:gate, [obligation(classification, decision_id, delta)]}
      :semantic_drift -> {:gate, [obligation(classification, decision_id, delta)]}
      :contradiction -> {:gate, [obligation(classification, decision_id, delta)]}
      :unresolved -> {:gate, [obligation(classification, decision_id, delta)]}
    end
  end

  defp obligation(:weakening, decision_id, delta) do
    DesignObligation.new(
      :weakening,
      decision_id,
      statement(delta, "Change to #{decision_id} weakens a load-bearing justification (e.g. a dropped REPORT / proof obligation)."),
      [
        "prove the weakened property is still preserved",
        "mark as an intentional, documented design shift",
        "reject the change"
      ]
    )
  end

  defp obligation(:semantic_drift, decision_id, delta) do
    DesignObligation.new(
      :semantic_drift,
      decision_id,
      statement(delta, "The governing principle of #{decision_id} changed; the design's meaning may have drifted."),
      [
        "prove the new principle subsumes the old",
        "mark as an intentional philosophical shift",
        "reject the change"
      ]
    )
  end

  defp obligation(:contradiction, decision_id, delta) do
    DesignObligation.new(
      :contradiction,
      decision_id,
      statement(delta, "The runtime behaviour of #{decision_id} now contradicts the prior version."),
      ["resolve the contradiction", "reject the change"]
    )
  end

  defp obligation(:orthogonal_extension, decision_id, delta) do
    DesignObligation.new(
      :orthogonal_extension,
      decision_id,
      statement(delta, "#{decision_id} gained an orthogonal extension; confirm it does not interact with existing guarantees."),
      ["confirm independence", "fold into an existing judgement"]
    )
  end

  defp obligation(:unresolved, decision_id, delta) do
    DesignObligation.new(
      :unresolved,
      decision_id,
      statement(delta, "The change to #{decision_id} could not be classified; manual review is required."),
      ["classify manually", "supply formal evidence", "reject the change"]
    )
  end

  defp statement(%{rationale: r}, prefix) when is_binary(r) and r != "", do: prefix <> " (" <> r <> ")"
  defp statement(_delta, prefix), do: prefix
end
