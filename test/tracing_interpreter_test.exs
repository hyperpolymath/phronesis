# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.TracingInterpreterTest do
  @moduledoc """
  Tests for the TracingInterpreter module.

  Per the semantic anchor: "All ethical decisions must produce an explicit trace structure."
  """

  use ExUnit.Case, async: true

  alias Phronesis.{State, Trace, TracingInterpreter}

  describe "execute/3 with constants" do
    test "traces constant binding" do
      source = "CONST x = 42"
      {:ok, ast} = Phronesis.parse(source)

      state = State.new()
      {:ok, state, trace} = TracingInterpreter.execute(ast, state)

      # Check state
      assert {:ok, 42} = State.lookup(state, "x")

      # Check trace
      assert trace.status == :completed
      assert length(trace.steps) >= 1

      # Find bind step
      bind_step = Enum.find(trace.steps, fn s -> s.type == :bind end)
      assert bind_step != nil
      assert bind_step.result == 42
    end

    test "traces arithmetic expression evaluation" do
      source = "CONST result = 10 + 5 * 2"
      {:ok, ast} = Phronesis.parse(source)

      state = State.new()
      {:ok, state, trace} = TracingInterpreter.execute(ast, state)

      # Check state
      assert {:ok, 20} = State.lookup(state, "result")

      # Check trace has eval steps
      eval_steps = Enum.filter(trace.steps, fn s -> s.type == :eval end)
      assert length(eval_steps) >= 1
    end
  end

  describe "execute/3 with policies" do
    test "traces policy registration" do
      source = """
      POLICY test_policy:
        value > 10
        THEN ACCEPT("Value is high")
        PRIORITY: 100
        EXPIRES: never
        CREATED_BY: test
      """

      {:ok, ast} = Phronesis.parse(source)
      state = State.new()

      {:ok, state, trace} = TracingInterpreter.execute(ast, state)

      # Policy should be registered
      assert {:ok, _policy} = State.get_policy(state, "test_policy")

      # Trace should record registration
      assert trace.status == :completed
    end
  end

  describe "evaluate_situation/2" do
    test "traces policy matching when condition is true" do
      source = """
      POLICY high_value:
        amount > 100
        THEN REJECT("Amount too high")
        PRIORITY: 100
        EXPIRES: never
        CREATED_BY: test
      """

      {:ok, ast} = Phronesis.parse(source)
      state = State.new(environment: %{"amount" => 150})

      {:ok, state, _setup_trace} = TracingInterpreter.execute(ast, state)
      {:ok, _state, trace} = TracingInterpreter.evaluate_situation(state)

      # Should have match step
      match_step = Enum.find(trace.steps, fn s -> s.type == :match end)
      assert match_step != nil
      assert match_step.result == true

      # Should have vote step (consensus)
      vote_step = Enum.find(trace.steps, fn s -> s.type == :vote end)
      assert vote_step != nil

      # Should have final decision
      assert trace.decision == {:reject, "Amount too high"}
    end

    test "traces policy not matching when condition is false" do
      source = """
      POLICY high_value:
        amount > 100
        THEN REJECT("Amount too high")
        PRIORITY: 100
        EXPIRES: never
        CREATED_BY: test
      """

      {:ok, ast} = Phronesis.parse(source)
      state = State.new(environment: %{"amount" => 50})

      {:ok, state, _setup_trace} = TracingInterpreter.execute(ast, state)
      {:ok, _state, trace} = TracingInterpreter.evaluate_situation(state)

      # Should have match step showing no match
      match_step = Enum.find(trace.steps, fn s -> s.type == :match end)
      assert match_step != nil
      assert match_step.result == false

      # No decision when no policy matches
      assert trace.decision == nil
    end

    test "evaluates multiple policies in priority order" do
      source = """
      POLICY low_priority:
        always_true == true
        THEN ACCEPT("Low priority accepted")
        PRIORITY: 10
        EXPIRES: never
        CREATED_BY: test

      POLICY high_priority:
        always_true == true
        THEN REJECT("High priority rejected")
        PRIORITY: 100
        EXPIRES: never
        CREATED_BY: test
      """

      {:ok, ast} = Phronesis.parse(source)
      state = State.new(environment: %{"always_true" => true})

      {:ok, state, _setup_trace} = TracingInterpreter.execute(ast, state)
      {:ok, _state, trace} = TracingInterpreter.evaluate_situation(state)

      # High priority policy should match first
      assert trace.decision == {:reject, "High priority rejected"}
    end
  end

  describe "consensus tracing" do
    test "traces multi-agent consensus" do
      source = """
      POLICY consensus_policy:
        requires_approval == true
        THEN ACCEPT("Approved by committee")
        PRIORITY: 100
        EXPIRES: never
        CREATED_BY: test
      """

      {:ok, ast} = Phronesis.parse(source)

      state =
        State.new(
          environment: %{"requires_approval" => true},
          agents: ["alice", "bob", "carol"],
          consensus_threshold: 0.67
        )

      {:ok, state, _setup_trace} = TracingInterpreter.execute(ast, state)
      {:ok, _state, trace} = TracingInterpreter.evaluate_situation(state)

      # Should have vote step with agent information
      vote_step = Enum.find(trace.steps, fn s -> s.type == :vote end)
      assert vote_step != nil
      assert vote_step.rationale =~ "3/3"
      assert vote_step.result == true
    end
  end

  describe "error tracing" do
    test "traces undefined variable error" do
      source = "CONST y = undefined_var + 1"
      {:ok, ast} = Phronesis.parse(source)

      state = State.new()
      {:error, reason, trace} = TracingInterpreter.execute(ast, state)

      assert {:undefined_variable, "undefined_var"} = reason
      assert trace.status == :failed

      # Should have error step
      error_step = Enum.find(trace.steps, fn s -> s.type == :error end)
      assert error_step != nil
    end
  end

  describe "trace format output" do
    test "produces readable trace for demo" do
      source = """
      CONST threshold = 50

      POLICY risk_check:
        risk_level > threshold
        THEN REJECT("Risk exceeds threshold")
        PRIORITY: 100
        EXPIRES: never
        CREATED_BY: demo
      """

      {:ok, ast} = Phronesis.parse(source)
      state = State.new(environment: %{"risk_level" => 75})

      {:ok, state, _setup_trace} = TracingInterpreter.execute(ast, state)
      {:ok, _state, trace} = TracingInterpreter.evaluate_situation(state)

      output = Trace.format(trace)

      # Should contain key information
      assert output =~ "PHRONESIS DECISION TRACE"
      assert output =~ "REJECT"
    end
  end
end
