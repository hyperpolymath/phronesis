# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.TraceTest do
  @moduledoc """
  Tests for the Trace module.

  Per the semantic anchor: "All ethical decisions must produce an explicit trace structure."
  """

  use ExUnit.Case, async: true

  alias Phronesis.Trace

  describe "Trace.new/1" do
    test "creates a trace with unique ID" do
      trace1 = Trace.new()
      trace2 = Trace.new()

      assert trace1.id != trace2.id
      assert trace1.status == :pending
      assert trace1.steps == []
      assert trace1.decision == nil
    end

    test "accepts custom ID" do
      trace = Trace.new(id: "custom-id-123")
      assert trace.id == "custom-id-123"
    end

    test "accepts metadata" do
      trace = Trace.new(metadata: %{policy: "test_policy"})
      assert trace.metadata == %{policy: "test_policy"}
    end
  end

  describe "Trace.step/5" do
    test "appends steps in order" do
      trace = Trace.new()
      trace = Trace.step(trace, :eval, %{expr: "x > 10"}, true, "15 > 10 is true")
      trace = Trace.step(trace, :match, %{policy: "high_risk"}, true, "Policy matched")

      assert length(trace.steps) == 2
      [step1, step2] = trace.steps

      assert step1.type == :eval
      assert step1.result == true

      assert step2.type == :match
      assert step2.inputs == %{policy: "high_risk"}
    end
  end

  describe "Trace convenience functions" do
    test "eval/4 records evaluation step" do
      trace = Trace.new()
      trace = Trace.eval(trace, {:identifier, "x"}, 42, "Variable lookup")

      [step] = trace.steps
      assert step.type == :eval
      assert step.result == 42
    end

    test "match/4 records policy match step" do
      trace = Trace.new()
      trace = Trace.match(trace, "test_policy", true, "Condition was true")

      [step] = trace.steps
      assert step.type == :match
      assert step.inputs == %{policy: "test_policy"}
      assert step.result == true
    end

    test "vote/5 records consensus vote step" do
      trace = Trace.new()
      votes = %{"alice" => true, "bob" => true, "carol" => false}
      trace = Trace.vote(trace, {:accept, nil}, votes, true, "2/3 approved")

      [step] = trace.steps
      assert step.type == :vote
      assert step.inputs.votes == votes
      assert step.result == true
    end

    test "action/4 records action execution step" do
      trace = Trace.new()
      trace = Trace.action(trace, {:reject, "High risk"}, :executed, "Action completed")

      [step] = trace.steps
      assert step.type == :action
    end

    test "bind/3 records variable binding" do
      trace = Trace.new()
      trace = Trace.bind(trace, "threshold", 50)

      [step] = trace.steps
      assert step.type == :bind
      assert step.inputs == %{name: "threshold"}
      assert step.result == 50
    end

    test "error/3 records error step" do
      trace = Trace.new()
      trace = Trace.error(trace, {:undefined_variable, "x"}, "Variable not found")

      [step] = trace.steps
      assert step.type == :error
      assert step.rationale == "Variable not found"
    end
  end

  describe "Trace.complete/2" do
    test "marks trace as completed with decision" do
      trace = Trace.new()
      trace = Trace.step(trace, :eval, %{}, true, "test")
      trace = Trace.complete(trace, {:accept, "All checks passed"})

      assert trace.status == :completed
      assert trace.decision == {:accept, "All checks passed"}
      assert trace.completed_at != nil
    end
  end

  describe "Trace.fail/2" do
    test "marks trace as failed with error" do
      trace = Trace.new()
      trace = Trace.fail(trace, {:parse_error, "Invalid syntax"})

      assert trace.status == :failed
      assert trace.decision == {:error, {:parse_error, "Invalid syntax"}}
      assert trace.completed_at != nil
    end
  end

  describe "Trace.format/1" do
    test "produces human-readable output" do
      trace = Trace.new(id: "test-trace-001")
      trace = Trace.eval(trace, {:identifier, "x"}, 42, "Variable lookup")
      trace = Trace.match(trace, "test_policy", true, "Policy matched")
      trace = Trace.complete(trace, {:accept, "Approved"})

      output = Trace.format(trace)

      assert output =~ "PHRONESIS DECISION TRACE"
      assert output =~ "test-trace-001"
      assert output =~ "ACCEPT"
      assert output =~ "EVAL"
      assert output =~ "MATCH"
    end
  end

  describe "Trace.to_map/1" do
    test "converts trace to JSON-serializable map" do
      trace = Trace.new(id: "test-001", metadata: %{source: "test"})
      trace = Trace.eval(trace, {:literal, :integer, 42}, 42, "Literal")
      trace = Trace.complete(trace, {:reject, "Failed"})

      map = Trace.to_map(trace)

      assert map.id == "test-001"
      assert map.status == :completed
      assert map.metadata == %{source: "test"}
      assert map.decision == %{type: "reject", reason: "Failed"}
      assert length(map.steps) == 1
    end
  end
end
