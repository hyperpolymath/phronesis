# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion do
  @moduledoc """
  Phronesis's reflexive design layer — *design self-relation*, not runtime reflection.

  The ordinary toolchain (parser → elaboration → type/effect/obligation checking →
  verification → runtime/reporting) compiles *programs*. The reflexion layer sits
  alongside it and compiles the language's *design rationale*: it turns toolchain
  artefacts into explicit claims, records why a design is held valid in a
  judgement-evidence graph, compares justification-paths across versions, and
  emits design obligations that gate changes to the language itself.

  Pipeline: **Build → Extract → Graph → Compare → Classify → Reevaluate → Gate.**

  It never auto-mutates semantics; the strongest thing it does is *gate* a change
  and require an explicit resolution. See `docs/REFLEXION.adoc` for the design.

  ## Example

      {:ok, result} = Phronesis.Reflexion.review(v1_source, v2_source)
      result.gate         #=> :permit | :warn | :gate
      result.obligations  #=> [%Phronesis.Reflexion.DesignObligation{...}]
  """

  alias Phronesis.Reflexion.{
    ClaimExtractor,
    DesignLedger,
    DesignObligation,
    Equivalence,
    InvariantPath,
    JudgementEvidenceGraph,
    Revaluation
  }

  @type review :: %{
          gate: Revaluation.gate(),
          deltas: [{String.t(), Equivalence.classification(), Revaluation.gate()}],
          obligations: [DesignObligation.t()],
          ledger: DesignLedger.t()
        }

  @doc """
  Run the full reflexion pipeline over two source versions of a policy program.

  For every decision (policy) present in both versions, it lifts the combined
  justification path, classifies the delta, revaluates it into a gate + any
  obligations, and records the outcome in an append-only design ledger. The
  overall gate is the most severe per-decision gate.
  """
  @spec review(String.t(), String.t()) :: {:ok, review()} | {:error, term()}
  def review(old_source, new_source) when is_binary(old_source) and is_binary(new_source) do
    with {:ok, old_claims} <- ClaimExtractor.extract_from_source(old_source),
         {:ok, new_claims} <- ClaimExtractor.extract_from_source(new_source) do
      subjects = common_subjects(old_claims, new_claims)

      {gate, obligations, ledger, deltas} =
        Enum.reduce(subjects, {:permit, [], DesignLedger.new(), []}, fn subject,
                                                                        {gate_acc, obs_acc, ledger,
                                                                         deltas_acc} ->
          old_path = InvariantPath.from_claims(old_claims, subject)
          new_path = InvariantPath.from_claims(new_claims, subject)
          delta = Equivalence.compare(old_path, new_path)
          {gate, obligations} = Revaluation.revaluate(delta, subject)

          ledger =
            ledger
            |> DesignLedger.append(:classification, Equivalence.to_map(delta), decision_id: subject)
            |> append_obligations(obligations, subject)

          {merge_gate(gate_acc, gate), obs_acc ++ obligations, ledger,
           deltas_acc ++ [{subject, delta.classification, gate}]}
        end)

      {:ok, %{gate: gate, deltas: deltas, obligations: obligations, ledger: ledger}}
    end
  end

  @doc "Build the judgement-evidence graph for a single source version."
  @spec graph(String.t()) :: {:ok, JudgementEvidenceGraph.t()} | {:error, term()}
  def graph(source) when is_binary(source) do
    with {:ok, claims} <- ClaimExtractor.extract_from_source(source) do
      {:ok, JudgementEvidenceGraph.from_claims(claims)}
    end
  end

  @doc """
  Demonstrate the pipeline: take a policy that uses the `REPORT` map-territory
  mandate, drop it in a second version, and show the resulting gate + obligation
  + tamper-evident ledger. Used by the `just reflexion-demo` recipe.
  """
  @spec demo() :: review()
  def demo do
    v1 = """
    POLICY warning_alert:
      severity >= 70 AND severity < 90
      THEN REPORT("Warning level severity")
      PRIORITY: 200
      EXPIRES: never
      CREATED_BY: monitoring
    """

    v2 = String.replace(v1, ~s|REPORT("Warning level severity")|, ~s|ACCEPT("Warning level severity")|)

    {:ok, result} = review(v1, v2)

    IO.puts("Reflexion review — overall gate: #{result.gate}")

    Enum.each(result.deltas, fn {subject, classification, gate} ->
      IO.puts("  #{subject}: #{classification} -> #{gate}")
    end)

    Enum.each(result.obligations, fn o ->
      IO.puts("  obligation [#{o.classification}] #{o.statement}")
      Enum.each(o.options, fn opt -> IO.puts("      • #{opt}") end)
    end)

    integrity = DesignLedger.verify(result.ledger)
    IO.puts("  ledger: #{length(DesignLedger.entries(result.ledger))} entries, integrity #{inspect(integrity)}")

    result
  end

  defp append_obligations(ledger, obligations, subject) do
    Enum.reduce(obligations, ledger, fn obligation, ledger ->
      DesignLedger.append(ledger, :obligation, DesignObligation.to_map(obligation), decision_id: subject)
    end)
  end

  defp common_subjects(old_claims, new_claims) do
    old_subjects = old_claims |> Enum.map(& &1.subject) |> MapSet.new()
    new_subjects = new_claims |> Enum.map(& &1.subject) |> MapSet.new()

    old_subjects |> MapSet.intersection(new_subjects) |> MapSet.to_list() |> Enum.sort()
  end

  defp merge_gate(:gate, _), do: :gate
  defp merge_gate(_, :gate), do: :gate
  defp merge_gate(:warn, _), do: :warn
  defp merge_gate(_, :warn), do: :warn
  defp merge_gate(_, _), do: :permit
end
