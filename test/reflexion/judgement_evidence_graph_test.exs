# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.JudgementEvidenceGraphTest do
  use ExUnit.Case, async: true

  alias Phronesis.Reflexion.{Claim, ClaimExtractor, JudgementEvidenceGraph}

  @report_policy """
  POLICY warning_alert:
    severity >= 70
    THEN REPORT("Warning level severity")
    PRIORITY: 200
    EXPIRES: never
    CREATED_BY: monitoring
  """

  test "from_claims makes one judgement and one typed evidence edge per claim" do
    claims = [
      Claim.obligation_discharge("policy p", "decision-completeness"),
      Claim.safety_preservation("policy p", "REPORT-adequacy", ["x > 1"])
    ]

    g = JudgementEvidenceGraph.from_claims(claims)

    assert map_size(g.judgements) == 2
    assert map_size(g.evidence) == 2
    assert length(g.edges) == 2
  end

  test "a REPORT (safety) claim produces a map_territory_report edge" do
    {:ok, claims} = ClaimExtractor.extract_from_source(@report_policy)
    g = JudgementEvidenceGraph.from_claims(claims)

    assert Enum.any?(g.edges, &(&1.kind == :map_territory_report))
  end

  test "evidence_for returns the evidence attached to a judgement" do
    {g, jid} = JudgementEvidenceGraph.add_judgement(JudgementEvidenceGraph.new(), "j")
    {g, _eid} = JudgementEvidenceGraph.add_evidence(g, jid, :human_note, "note")

    assert [%{kind: :human_note, label: "note"}] = JudgementEvidenceGraph.evidence_for(g, jid)
  end

  test "to_map is serialisable" do
    g = JudgementEvidenceGraph.from_claims([Claim.provenance("const x", "1")])
    assert %{judgements: [_], evidence: [_], edges: [_]} = JudgementEvidenceGraph.to_map(g)
  end
end
