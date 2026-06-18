# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.EquivalenceTest do
  use ExUnit.Case, async: true

  alias Phronesis.Reflexion.Equivalence

  defp classify(old, new), do: Equivalence.compare(old, new).classification

  test "identical paths are equivalent" do
    path = [{:principle, "practical-judgement"}, {:static_rule, "decision-completeness"}]
    assert classify(path, path) == :equivalent
  end

  test "a changed principle is semantic drift" do
    old = [{:principle, "epistemic-safety"}, {:static_rule, "r"}]
    new = [{:principle, "practical-judgement"}, {:static_rule, "r"}]
    assert classify(old, new) == :semantic_drift
  end

  test "accept-vs-reject runtime is a contradiction" do
    old = [{:principle, "p"}, {:runtime_behaviour, "decision:accept"}]
    new = [{:principle, "p"}, {:runtime_behaviour, "decision:reject"}]
    assert classify(old, new) == :contradiction
  end

  test "dropping a load-bearing step is a weakening" do
    old = [{:principle, "p"}, {:proof_obligation, "o"}, {:audit_trace, "REPORT:x"}]
    new = [{:principle, "p"}, {:proof_obligation, "o"}]
    assert classify(old, new) == :weakening
  end

  test "adding a load-bearing step is a strengthening" do
    old = [{:principle, "p"}]
    new = [{:principle, "p"}, {:proof_obligation, "o"}]
    assert classify(old, new) == :strengthening
  end

  test "additive detail within existing dimensions is a refinement" do
    old = [{:principle, "p"}, {:construct, "a"}]
    new = [{:principle, "p"}, {:construct, "a"}, {:construct, "b"}]
    assert classify(old, new) == :refinement
  end

  test "extending into a new non-load-bearing dimension is an orthogonal extension" do
    old = [{:principle, "p"}, {:construct, "a"}]
    new = [{:principle, "p"}, {:construct, "a"}, {:runtime_behaviour, "x"}]
    assert classify(old, new) == :orthogonal_extension
  end

  test "an unclassifiable add+remove falls to unresolved" do
    old = [{:principle, "p"}, {:construct, "a"}]
    new = [{:principle, "p"}, {:runtime_behaviour, "x"}]
    assert classify(old, new) == :unresolved
  end

  test "delta carries added/removed steps and a rationale, and is serialisable" do
    old = [{:principle, "p"}, {:proof_obligation, "o"}]
    new = [{:principle, "p"}]
    delta = Equivalence.compare(old, new)
    assert {:proof_obligation, "o"} in delta.removed
    assert is_binary(delta.rationale)
    assert %{classification: :weakening} = Equivalence.to_map(delta)
  end
end
