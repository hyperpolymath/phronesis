# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Debugger do
  @moduledoc """
  Interactive debugger for Phronesis policies.

  Provides breakpoint management, step execution, state inspection,
  and distributed consensus tracing.

  ## Features

  - Set breakpoints on policies, lines, or conditions
  - Step through execution (step, next, continue, finish)
  - Inspect variables, routes, consensus votes
  - Trace distributed decision-making
  - Watch expressions
  - Call stack navigation

  ## Usage

      # Start debugging a policy file
      {:ok, session} = Debugger.start("policy.phr")

      # Set breakpoints
      Debugger.set_breakpoint(session, policy: "validate_route")
      Debugger.set_breakpoint(session, line: 42)

      # Run until breakpoint
      Debugger.continue(session)

      # Inspect state
      Debugger.inspect_var(session, "route")
      Debugger.show_stack(session)

      # Step execution
      Debugger.step(session)
      Debugger.next(session)
  """

  alias Phronesis.{Lexer, Parser, TracingInterpreter, State, Trace}

  defstruct [
    :file,
    :ast,
    :state,
    :trace,
    :breakpoints,
    :watches,
    :call_stack,
    :current_position,
    :mode,
    :history
  ]

  @type breakpoint :: {:policy, String.t()} | {:line, integer()} | {:condition, term()}
  @type step_mode :: :step | :next | :continue | :finish

  @type t :: %__MODULE__{
          file: String.t(),
          ast: [term()],
          state: State.t(),
          trace: Trace.t(),
          breakpoints: MapSet.t(breakpoint()),
          watches: %{String.t() => term()},
          call_stack: [term()],
          current_position: term() | nil,
          mode: step_mode(),
          history: [term()]
        }

  ## Session Management

  @doc """
  Start a debugging session for a policy file.
  """
  def start(file_path) do
    with {:ok, source} <- File.read(file_path),
         {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      session = %__MODULE__{
        file: file_path,
        ast: ast,
        state: State.new(),
        trace: Trace.new(),
        breakpoints: MapSet.new(),
        watches: %{},
        call_stack: [],
        current_position: nil,
        mode: :continue,
        history: []
      }

      {:ok, session}
    else
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Load additional context (routes, consensus state) into the session.
  """
  def load_context(session, context) do
    state = Map.merge(session.state, context)
    %{session | state: state}
  end

  ## Breakpoint Management

  @doc """
  Set a breakpoint by policy name, line number, or condition.

  ## Examples

      set_breakpoint(session, policy: "validate_route")
      set_breakpoint(session, line: 42)
      set_breakpoint(session, condition: {:var_equals, "status", :invalid})
  """
  def set_breakpoint(session, opts) do
    breakpoint = normalize_breakpoint(opts)
    breakpoints = MapSet.put(session.breakpoints, breakpoint)
    %{session | breakpoints: breakpoints}
  end

  @doc """
  Remove a breakpoint.
  """
  def remove_breakpoint(session, opts) do
    breakpoint = normalize_breakpoint(opts)
    breakpoints = MapSet.delete(session.breakpoints, breakpoint)
    %{session | breakpoints: breakpoints}
  end

  @doc """
  List all active breakpoints.
  """
  def list_breakpoints(session) do
    MapSet.to_list(session.breakpoints)
  end

  @doc """
  Clear all breakpoints.
  """
  def clear_breakpoints(session) do
    %{session | breakpoints: MapSet.new()}
  end

  defp normalize_breakpoint(policy: name), do: {:policy, name}
  defp normalize_breakpoint(line: num), do: {:line, num}
  defp normalize_breakpoint(condition: cond), do: {:condition, cond}

  ## Execution Control

  @doc """
  Continue execution until next breakpoint or completion.
  """
  def continue(session) do
    session = %{session | mode: :continue}
    run_until_break(session)
  end

  @doc """
  Step into next statement (enters function calls).
  """
  def step(session) do
    session = %{session | mode: :step}
    execute_one_step(session)
  end

  @doc """
  Step over next statement (doesn't enter function calls).
  """
  def next(session) do
    session = %{session | mode: :next}
    execute_one_step(session)
  end

  @doc """
  Finish current function and break at return.
  """
  def finish(session) do
    session = %{session | mode: :finish}
    run_until_return(session)
  end

  @doc """
  Run policy to completion (ignore breakpoints).
  """
  def run(session) do
    case TracingInterpreter.execute(session.ast, session.state) do
      {:ok, result_state, trace} ->
        session = %{session | state: result_state, trace: trace}
        {:ok, session, result_state}

      {:error, reason} ->
        {:error, reason}
    end
  end

  ## State Inspection

  @doc """
  Inspect a variable in the current scope.
  """
  def inspect_var(session, var_name) do
    case Map.fetch(session.state.variables, var_name) do
      {:ok, value} -> {:ok, value}
      :error -> {:error, :not_found}
    end
  end

  @doc """
  List all variables in current scope.
  """
  def list_vars(session) do
    session.state.variables
  end

  @doc """
  Show the current call stack.
  """
  def show_stack(session) do
    session.call_stack
  end

  @doc """
  Show the execution trace so far.
  """
  def show_trace(session) do
    Trace.format(session.trace)
  end

  @doc """
  Add a watch expression.
  """
  def add_watch(session, name, expression) do
    watches = Map.put(session.watches, name, expression)
    %{session | watches: watches}
  end

  @doc """
  Evaluate all watch expressions.
  """
  def eval_watches(session) do
    Enum.map(session.watches, fn {name, expr} ->
      {name, evaluate_watch(expr, session.state)}
    end)
  end

  @doc """
  Get current source position.
  """
  def current_position(session) do
    session.current_position
  end

  ## Internal Execution

  defp run_until_break(session) do
    # Execute AST with breakpoint checking
    execute_with_breaks(session, session.ast)
  end

  defp execute_one_step(session) do
    case session.ast do
      [] ->
        {:done, session}

      [node | rest] ->
        {new_state, new_trace} = execute_node(node, session.state, session.trace)

        session = %{
          session
          | ast: rest,
            state: new_state,
            trace: new_trace,
            current_position: node
        }

        {:ok, session}
    end
  end

  defp run_until_return(session) do
    initial_depth = length(session.call_stack)

    execute_until(session, fn sess ->
      length(sess.call_stack) < initial_depth
    end)
  end

  defp execute_with_breaks(session, []) do
    {:done, session}
  end

  defp execute_with_breaks(session, [node | rest]) do
    if should_break?(node, session) do
      session = %{session | ast: [node | rest], current_position: node}
      {:break, session, node}
    else
      {new_state, new_trace} = execute_node(node, session.state, session.trace)

      session = %{
        session
        | state: new_state,
          trace: new_trace,
          current_position: node,
          history: [node | session.history]
      }

      execute_with_breaks(session, rest)
    end
  end

  defp execute_until(session, condition_fn) do
    if condition_fn.(session) do
      {:ok, session}
    else
      case execute_one_step(session) do
        {:ok, new_session} -> execute_until(new_session, condition_fn)
        {:done, session} -> {:done, session}
      end
    end
  end

  defp should_break?(node, session) do
    Enum.any?(session.breakpoints, fn bp ->
      matches_breakpoint?(node, bp, session)
    end)
  end

  defp matches_breakpoint?({:policy, name, _cond, _action, _meta}, {:policy, bp_name}, _session) do
    name == bp_name
  end

  defp matches_breakpoint?(node, {:line, line_num}, _session) do
    extract_line(node) == line_num
  end

  defp matches_breakpoint?(_node, {:condition, cond_expr}, session) do
    evaluate_condition(cond_expr, session.state)
  end

  defp matches_breakpoint?(_, _, _), do: false

  defp execute_node(node, state, trace) do
    case TracingInterpreter.execute([node], state) do
      {:ok, new_state, new_trace} -> {new_state, Trace.merge(trace, new_trace)}
      {:error, _reason} -> {state, trace}
    end
  end

  defp extract_line({_type, _name, _args, _body, metadata}), do: metadata[:line]
  defp extract_line(_), do: nil

  defp evaluate_condition({:var_equals, var_name, expected}, state) do
    Map.get(state.variables, var_name) == expected
  end

  defp evaluate_condition({:var_matches, var_name, pattern}, state) do
    value = Map.get(state.variables, var_name)
    matches_pattern?(value, pattern)
  end

  defp evaluate_condition(_, _), do: false

  defp matches_pattern?(value, pattern) when is_function(pattern) do
    pattern.(value)
  end

  defp matches_pattern?(value, pattern), do: value == pattern

  defp evaluate_watch(expr, state) do
    # Simple variable lookup for now
    # Could be extended to full expression evaluation
    Map.get(state.variables, expr, :undefined)
  end

  ## Pretty Printing

  @doc """
  Format current debugger state for display.
  """
  def format_state(session) do
    """
    === Debugger State ===
    File: #{session.file}
    Mode: #{session.mode}
    Breakpoints: #{MapSet.size(session.breakpoints)}
    Call Stack Depth: #{length(session.call_stack)}
    Current Position: #{format_position(session.current_position)}
    Variables: #{map_size(session.state.variables)}
    Watches: #{map_size(session.watches)}
    """
  end

  defp format_position(nil), do: "N/A"

  defp format_position({:policy, name, _cond, _action, meta}) do
    "POLICY #{name} (line #{meta[:line] || "?"})"
  end

  defp format_position({:const, name, _value, meta}) do
    "CONST #{name} (line #{meta[:line] || "?"})"
  end

  defp format_position(_), do: "Unknown"
end
