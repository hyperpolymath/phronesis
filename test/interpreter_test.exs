# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.InterpreterTest do
  use ExUnit.Case

  alias Phronesis.{Interpreter, State}

  defp parse_and_execute(source, state \\ State.new()) do
    with {:ok, ast} <- Phronesis.parse(source) do
      Interpreter.execute(ast, state)
    end
  end

  describe "execute/2 - constants" do
    test "binds constants to environment" do
      {:ok, state} = parse_and_execute("CONST x = 42")
      assert {:ok, 42} = State.lookup(state, "x")
    end

    test "evaluates arithmetic expressions" do
      {:ok, state} = parse_and_execute("CONST result = 10 + 5 * 2")
      assert {:ok, 20} = State.lookup(state, "result")
    end

    test "evaluates boolean expressions" do
      {:ok, state} = parse_and_execute("CONST flag = true AND false")
      assert {:ok, false} = State.lookup(state, "flag")
    end
  end

  describe "execute/2 - policies" do
    test "registers policies in policy table" do
      source = """
      POLICY test_policy:
        x == 1
        THEN ACCEPT()
        PRIORITY: 100
      """

      {:ok, state} = parse_and_execute(source)
      assert {:ok, {:policy, "test_policy", _, _, _}} = State.get_policy(state, "test_policy")
    end

    test "sorts policies by priority" do
      source = """
      POLICY low_priority:
        true
        THEN ACCEPT()
        PRIORITY: 10

      POLICY high_priority:
        true
        THEN REJECT()
        PRIORITY: 100
      """

      {:ok, state} = parse_and_execute(source)
      [first | _] = State.policies_by_priority(state)
      assert {:policy, "high_priority", _, _, _} = first
    end
  end

  describe "evaluate_policy/2" do
    test "returns match when condition is true" do
      source = """
      POLICY always_match:
        true
        THEN ACCEPT()
        PRIORITY: 1
      """

      {:ok, state} = parse_and_execute(source)
      {:ok, policy} = State.get_policy(state, "always_match")

      assert {:ok, :match, {:accept, nil}, _} = Interpreter.evaluate_policy(policy, state)
    end

    test "returns no_match when condition is false" do
      source = """
      POLICY never_match:
        false
        THEN ACCEPT()
        PRIORITY: 1
      """

      {:ok, state} = parse_and_execute(source)
      {:ok, policy} = State.get_policy(state, "never_match")

      assert {:ok, :no_match, _} = Interpreter.evaluate_policy(policy, state)
    end

    test "evaluates condition with environment" do
      source = """
      CONST threshold = 50
      POLICY check_threshold:
        threshold > 40
        THEN ACCEPT()
        PRIORITY: 1
      """

      {:ok, state} = parse_and_execute(source)
      {:ok, policy} = State.get_policy(state, "check_threshold")

      assert {:ok, :match, _, _} = Interpreter.evaluate_policy(policy, state)
    end
  end

  describe "execute_action/2" do
    test "executes ACCEPT action with consensus" do
      state = State.new(agents: ["local"])

      {:ok, result, new_state} =
        Interpreter.execute_action({:accept, {:literal, :string, "approved"}}, state)

      assert {:accepted, "approved"} = result
      assert [log_entry | _] = new_state.consensus_log
      assert log_entry.result == :approved
    end

    test "executes REJECT action with consensus" do
      state = State.new(agents: ["local"])

      {:ok, result, new_state} =
        Interpreter.execute_action({:reject, {:literal, :string, "denied"}}, state)

      assert {:rejected, "denied"} = result
      assert [log_entry | _] = new_state.consensus_log
      assert log_entry.result == :approved
    end

    test "logs all executed actions" do
      state = State.new(agents: ["local"])

      {:ok, _, state} =
        Interpreter.execute_action({:accept, nil}, state)

      {:ok, _, state} =
        Interpreter.execute_action({:reject, nil}, state)

      assert length(state.consensus_log) == 2
    end
  end

  describe "consensus" do
    test "requires consensus for action execution" do
      # With no agents, consensus auto-approves
      state = State.new(agents: [])

      {:ok, _, _} = Interpreter.execute_action({:accept, nil}, state)
    end

    test "logs vote results" do
      state = State.new(agents: ["agent1", "agent2"])

      {:ok, _, new_state} = Interpreter.execute_action({:accept, nil}, state)

      [log_entry | _] = new_state.consensus_log
      assert Map.has_key?(log_entry.votes, "agent1")
      assert Map.has_key?(log_entry.votes, "agent2")
    end
  end

  describe "block actions" do
    test "executes all actions in block" do
      state = State.new(agents: ["local"])

      block = {:block, [
        {:report, {:literal, :string, "first"}},
        {:report, {:literal, :string, "second"}},
        {:accept, nil}
      ]}

      {:ok, result, _} = Interpreter.execute_action(block, state)
      assert {:accepted, nil} = result
    end
  end

  describe "conditional actions" do
    test "executes then branch when condition is true" do
      state = State.new(agents: ["local"])
      state = State.bind(state, "x", 1)

      conditional = {:conditional,
        {:comparison, :eq, {:identifier, "x"}, {:literal, :integer, 1}},
        {:accept, {:literal, :string, "yes"}},
        {:reject, {:literal, :string, "no"}}
      }

      {:ok, result, _} = Interpreter.execute_action(conditional, state)
      assert {:accepted, "yes"} = result
    end

    test "executes else branch when condition is false" do
      state = State.new(agents: ["local"])
      state = State.bind(state, "x", 2)

      conditional = {:conditional,
        {:comparison, :eq, {:identifier, "x"}, {:literal, :integer, 1}},
        {:accept, {:literal, :string, "yes"}},
        {:reject, {:literal, :string, "no"}}
      }

      {:ok, result, _} = Interpreter.execute_action(conditional, state)
      assert {:rejected, "no"} = result
    end
  end
end
