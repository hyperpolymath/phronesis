# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.ClaimExtractorTest do
  use ExUnit.Case, async: true

  alias Phronesis.Reflexion.ClaimExtractor

  @report_policy """
  POLICY warning_alert:
    severity >= 70
    THEN REPORT("Warning level severity")
    PRIORITY: 200
    EXPIRES: never
    CREATED_BY: monitoring
  """

  @const_only "CONST threshold = 50\n"

  test "a policy whose action uses REPORT yields a REPORT-adequacy safety claim" do
    {:ok, claims} = ClaimExtractor.extract_from_source(@report_policy)

    safety = Enum.filter(claims, &(&1.kind == :safety_preservation))
    assert [claim] = safety
    assert claim.object == "REPORT-adequacy"
    assert claim.subject == "policy warning_alert"
    assert claim.predicate == "preserves"
    # the match condition is carried as the condition under which the property holds
    assert claim.conditions != []
  end

  test "a const-only program yields provenance claims and no safety claims" do
    {:ok, claims} = ClaimExtractor.extract_from_source(@const_only)

    assert Enum.any?(claims, &(&1.kind == :provenance and &1.subject == "const threshold"))
    refute Enum.any?(claims, &(&1.kind == :safety_preservation))
  end

  test "a non-REPORT policy yields an obligation-discharge claim but no safety claim" do
    src = String.replace(@report_policy, ~s|REPORT("Warning level severity")|, ~s|ACCEPT("ok")|)
    {:ok, claims} = ClaimExtractor.extract_from_source(src)

    assert Enum.any?(claims, &(&1.kind == :obligation_discharge))
    refute Enum.any?(claims, &(&1.kind == :safety_preservation))
  end

  test "parse errors propagate" do
    assert {:error, _} = ClaimExtractor.extract_from_source("this is not phronesis")
  end
end
