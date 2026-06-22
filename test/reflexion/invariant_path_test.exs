# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.InvariantPathTest do
  use ExUnit.Case, async: true

  alias Phronesis.Reflexion.{Claim, ClaimExtractor, InvariantPath, JudgementEvidenceGraph}

  @report_policy """
  POLICY warning_alert:
    severity >= 70
    THEN REPORT("Warning level severity")
    PRIORITY: 200
    EXPIRES: never
    CREATED_BY: monitoring
  """

  test "steps are filtered to known stages and ordered canonically" do
    path = InvariantPath.new("d", [{:audit_trace, "a"}, {:principle, "p"}, {:bogus, "x"}])
    stages = Enum.map(path.steps, fn {stage, _} -> stage end)
    assert stages == [:principle, :audit_trace]
  end

  test "a REPORT policy's combined path carries an audit_trace step" do
    {:ok, claims} = ClaimExtractor.extract_from_source(@report_policy)
    path = InvariantPath.from_claims(claims, "policy warning_alert")
    stages = Enum.map(path.steps, fn {stage, _} -> stage end)

    assert :audit_trace in stages
    assert :principle in stages
  end

  test "from_jeg lifts a judgement and its evidence into an ordered path" do
    claims = [Claim.safety_preservation("policy p", "REPORT-adequacy", ["x > 1"])]
    g = JudgementEvidenceGraph.from_claims(claims)
    [jid] = Map.keys(g.judgements)

    path = InvariantPath.from_jeg(g, jid)
    stages = Enum.map(path.steps, fn {stage, _} -> stage end)

    assert List.first(stages) == :principle
    assert :audit_trace in stages
  end
end
