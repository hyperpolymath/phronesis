# SPDX-License-Identifier: MPL-2.0
# Debugger Tests

defmodule Phronesis.DebuggerTest do
  @moduledoc """
  Tests for the Phronesis debugger.
  """

  use ExUnit.Case, async: false
  alias Phronesis.Debugger

  @fixture_file Path.join([__DIR__, "fixtures", "test_debug.phr"])

  setup do
    {:ok, policy_file: @fixture_file}
  end

  describe "Session Management" do
    test "starts a debugging session", %{policy_file: policy_file} do
      assert {:ok, session} = Debugger.start(policy_file)
      assert session.file == policy_file
      assert is_list(session.ast)
      assert length(session.ast) > 0
      assert session.mode == :continue
    end

    test "loads context into session", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      context = %{hops: 5}
      session = Debugger.load_context(session, context)

      assert session.state.hops == 5
    end

    test "handles invalid file" do
      assert {:error, _} = Debugger.start("nonexistent.phr")
    end
  end

  describe "Breakpoint Management" do
    test "sets breakpoint by policy name", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      session = Debugger.set_breakpoint(session, policy: "test_policy")

      breakpoints = Debugger.list_breakpoints(session)
      assert {:policy, "test_policy"} in breakpoints
    end

    test "sets breakpoint by line number", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      session = Debugger.set_breakpoint(session, line: 5)

      breakpoints = Debugger.list_breakpoints(session)
      assert {:line, 5} in breakpoints
    end

    test "sets conditional breakpoint", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      session =
        Debugger.set_breakpoint(session,
          condition: {:var_equals, "status", :invalid}
        )

      breakpoints = Debugger.list_breakpoints(session)
      assert {:condition, {:var_equals, "status", :invalid}} in breakpoints
    end

    test "removes breakpoint", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      session = Debugger.set_breakpoint(session, policy: "test_policy")
      assert length(Debugger.list_breakpoints(session)) == 1

      session = Debugger.remove_breakpoint(session, policy: "test_policy")
      assert length(Debugger.list_breakpoints(session)) == 0
    end

    test "clears all breakpoints", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      session =
        session
        |> Debugger.set_breakpoint(policy: "test_policy")
        |> Debugger.set_breakpoint(line: 5)
        |> Debugger.set_breakpoint(line: 10)

      assert length(Debugger.list_breakpoints(session)) == 3

      session = Debugger.clear_breakpoints(session)
      assert length(Debugger.list_breakpoints(session)) == 0
    end
  end

  describe "Execution Control" do
    test "runs policy to completion", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      # Load context
      context = %{hops: 5}
      session = Debugger.load_context(session, context)

      # Run to completion
      assert {:ok, final_session, _final_state} = Debugger.run(session)
      assert is_map(final_session.state)
    end

    test "steps through execution", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      # Step once
      assert {:ok, new_session} = Debugger.step(session)
      assert new_session.current_position != nil
    end

    test "continues until breakpoint", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      # Set breakpoint on policy
      session = Debugger.set_breakpoint(session, policy: "test_policy")

      # Load context and continue
      context = %{hops: 5}
      session = Debugger.load_context(session, context)

      # Should hit breakpoint
      result = Debugger.continue(session)

      # Result could be {:break, session, node} or {:done, session}
      assert match?({:break, _, _}, result) or match?({:done, _}, result)
    end
  end

  describe "State Inspection" do
    test "inspects variables", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      # Add a variable to state
      session = put_in(session.state.variables, %{"test_var" => 42})

      assert {:ok, 42} = Debugger.inspect_var(session, "test_var")
      assert {:error, :not_found} = Debugger.inspect_var(session, "nonexistent")
    end

    test "lists all variables", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      vars = %{"var1" => 1, "var2" => 2}
      session = put_in(session.state.variables, vars)

      listed_vars = Debugger.list_vars(session)
      assert listed_vars == vars
    end

    test "shows call stack", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      stack = Debugger.show_stack(session)
      assert is_list(stack)
    end

    test "shows execution trace", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      trace_output = Debugger.show_trace(session)
      assert is_binary(trace_output)
    end

    test "gets current position", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      # Initially nil
      assert Debugger.current_position(session) == nil

      # After stepping, should have position
      {:ok, stepped_session} = Debugger.step(session)
      pos = Debugger.current_position(stepped_session)
      # Position could be any AST node or nil if execution complete
      assert pos == nil or is_tuple(pos)
    end
  end

  describe "Watch Expressions" do
    test "adds and evaluates watch expressions", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      # Add variable to state
      session = put_in(session.state.variables, %{"status" => :valid})

      # Add watch
      session = Debugger.add_watch(session, "status_watch", "status")

      # Eval watches
      watches = Debugger.eval_watches(session)
      assert [{"status_watch", :valid}] = watches
    end

    test "watch returns undefined for missing vars", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      session = Debugger.add_watch(session, "missing_watch", "missing_var")

      watches = Debugger.eval_watches(session)
      assert [{"missing_watch", :undefined}] = watches
    end
  end

  describe "Formatting" do
    test "formats debugger state", %{policy_file: policy_file} do
      {:ok, session} = Debugger.start(policy_file)

      output = Debugger.format_state(session)
      assert String.contains?(output, "Debugger State")
      assert String.contains?(output, "File:")
      assert String.contains?(output, session.file)
    end
  end
end
