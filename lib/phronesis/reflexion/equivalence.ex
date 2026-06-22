# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.Equivalence do
  @moduledoc """
  The Invariant-Path equivalence engine: compares two justification paths and
  classifies the delta.

  A normal compiler can tell you whether both versions type-check; a proof
  assistant whether each preserves a theorem. This engine asks a different
  question — *are these the same design claim under a harmless refactor, or has
  the design's ethical/epistemic meaning changed?* — and answers with one of:

      equivalent | refinement | weakening | strengthening
      orthogonal_extension | semantic_drift | contradiction | unresolved

  The classifier is a deterministic heuristic over the path's `{stage, label}`
  steps. Genuinely ambiguous cases fall to `:unresolved` — the safe default,
  which the revaluation loop gates for human/tool review. (Formal semantic
  equivalence via the proof layer is a documented future hardening.)
  """

  alias Phronesis.Reflexion.InvariantPath

  @type classification ::
          :equivalent
          | :refinement
          | :weakening
          | :strengthening
          | :orthogonal_extension
          | :semantic_drift
          | :contradiction
          | :unresolved

  @type delta :: %{
          classification: classification(),
          added: [InvariantPath.step()],
          removed: [InvariantPath.step()],
          rationale: String.t()
        }

  # stages whose removal weakens (or whose addition strengthens) the justification
  @load_bearing [:proof_obligation, :static_rule, :audit_trace]

  @doc "Compare two justification paths (or two raw step lists)."
  @spec compare(InvariantPath.t() | [InvariantPath.step()], InvariantPath.t() | [InvariantPath.step()]) ::
          delta()
  def compare(%InvariantPath{steps: old}, %InvariantPath{steps: new}), do: compare(old, new)

  def compare(old, new) when is_list(old) and is_list(new) do
    old_set = MapSet.new(old)
    new_set = MapSet.new(new)
    removed = old_set |> MapSet.difference(new_set) |> MapSet.to_list()
    added = new_set |> MapSet.difference(old_set) |> MapSet.to_list()

    classification = classify(old, new, removed, added)
    %{classification: classification, added: added, removed: removed, rationale: rationale(classification)}
  end

  @doc "A JSON-serialisable map of a delta."
  @spec to_map(delta()) :: map()
  def to_map(%{classification: c, added: added, removed: removed, rationale: r}) do
    %{
      classification: c,
      added: Enum.map(added, &step_to_map/1),
      removed: Enum.map(removed, &step_to_map/1),
      rationale: r
    }
  end

  # --- classification ---------------------------------------------------------

  defp classify(old, new, removed, added) do
    cond do
      removed == [] and added == [] -> :equivalent
      principle_changed?(old, new) -> :semantic_drift
      contradictory_runtime?(old, new) -> :contradiction
      load_bearing?(removed) -> :weakening
      removed == [] and load_bearing?(added) -> :strengthening
      removed == [] and added != [] -> additive_kind(old, added)
      true -> :unresolved
    end
  end

  defp additive_kind(old, added) do
    old_stages = old |> stages() |> MapSet.new()
    added_stages = added |> stages() |> MapSet.new()

    if MapSet.subset?(added_stages, old_stages) do
      :refinement
    else
      :orthogonal_extension
    end
  end

  defp load_bearing?(steps), do: Enum.any?(stages(steps), &(&1 in @load_bearing))

  defp stages(steps), do: Enum.map(steps, fn {stage, _label} -> stage end)

  defp principle_changed?(old, new) do
    po = label_at(old, :principle)
    pn = label_at(new, :principle)
    po != nil and pn != nil and po != pn
  end

  defp contradictory_runtime?(old, new) do
    ro = label_at(old, :runtime_behaviour)
    rn = label_at(new, :runtime_behaviour)

    with wo when not is_nil(wo) <- decision_word(ro),
         wn when not is_nil(wn) <- decision_word(rn) do
      wo != wn
    else
      _ -> false
    end
  end

  defp label_at(steps, target) do
    Enum.find_value(steps, fn
      {^target, label} -> label
      _ -> nil
    end)
  end

  defp decision_word(nil), do: nil

  defp decision_word(label) when is_binary(label) do
    cond do
      String.contains?(label, "accept") -> :accept
      String.contains?(label, "reject") -> :reject
      true -> nil
    end
  end

  defp step_to_map({stage, label}), do: %{stage: stage, label: label}

  defp rationale(:equivalent), do: "Justification paths are identical; harmless under refactoring."
  defp rationale(:refinement), do: "Additive detail within existing justification dimensions."
  defp rationale(:strengthening), do: "Added a load-bearing justification (proof obligation / static rule / audit trace)."
  defp rationale(:weakening), do: "Removed a load-bearing justification (e.g. a dropped REPORT / proof obligation)."
  defp rationale(:orthogonal_extension), do: "Extended into a new, previously-absent justification dimension."
  defp rationale(:semantic_drift), do: "The governing principle changed; design meaning may have drifted."
  defp rationale(:contradiction), do: "Runtime behaviour now contradicts the prior version."
  defp rationale(:unresolved), do: "Delta could not be classified heuristically; manual review required."
end
