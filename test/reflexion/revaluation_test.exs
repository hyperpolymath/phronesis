# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.RevaluationTest do
  use ExUnit.Case, async: true

  alias Phronesis.Reflexion.Revaluation

  defp delta(classification), do: %{classification: classification, added: [], removed: [], rationale: ""}

  test "weakening gates and emits an obligation with the three resolutions" do
    {gate, [obligation]} = Revaluation.revaluate(delta(:weakening), "policy p")
    assert gate == :gate
    assert obligation.classification == :weakening
    assert length(obligation.options) == 3
    assert "reject the change" in obligation.options
  end

  test "refinement permits with no obligation" do
    assert {:permit, []} = Revaluation.revaluate(delta(:refinement), "policy p")
  end

  test "strengthening and equivalent both permit" do
    assert {:permit, []} = Revaluation.revaluate(delta(:strengthening), "policy p")
    assert {:permit, []} = Revaluation.revaluate(delta(:equivalent), "policy p")
  end

  test "orthogonal extension warns" do
    assert {:warn, [_]} = Revaluation.revaluate(delta(:orthogonal_extension), "policy p")
  end

  test "unresolved gates for manual review" do
    assert {:gate, [_]} = Revaluation.revaluate(delta(:unresolved), "policy p")
  end
end
