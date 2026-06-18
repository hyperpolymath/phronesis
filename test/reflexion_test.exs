# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.ReflexionTest do
  use ExUnit.Case, async: true

  alias Phronesis.Reflexion
  alias Phronesis.Reflexion.DesignLedger

  @v1 """
  POLICY warning_alert:
    severity >= 70 AND severity < 90
    THEN REPORT("Warning level severity")
    PRIORITY: 200
    EXPIRES: never
    CREATED_BY: monitoring
  """

  # identical to @v1 but the REPORT map-territory mandate is dropped for a plain ACCEPT
  @v2 String.replace(@v1, ~s|REPORT("Warning level severity")|, ~s|ACCEPT("Warning level severity")|)

  test "an identical program permits with no obligations" do
    {:ok, result} = Reflexion.review(@v1, @v1)
    assert result.gate == :permit
    assert result.obligations == []
  end

  test "dropping a REPORT mandate is weakened and gated, with an obligation and ledger entries" do
    {:ok, result} = Reflexion.review(@v1, @v2)

    assert result.gate == :gate
    assert [{"policy warning_alert", :weakening, :gate}] = result.deltas
    assert [obligation] = result.obligations
    assert obligation.classification == :weakening

    # the change is recorded in a tamper-evident, append-only ledger
    assert DesignLedger.verify(result.ledger) == :ok
    assert length(DesignLedger.entries(result.ledger)) >= 2
  end

  test "graph/1 builds a judgement-evidence graph for a source version" do
    {:ok, graph} = Reflexion.graph(@v1)
    assert map_size(graph.judgements) > 0
    assert Enum.any?(graph.edges, &(&1.kind == :map_territory_report))
  end

  test "parse errors propagate from review/2" do
    assert {:error, _} = Reflexion.review("not phronesis", @v1)
  end
end
