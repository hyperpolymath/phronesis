# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Debugger.REPL do
  @moduledoc """
  Interactive debugger REPL for Phronesis.

  Provides a command-line interface for debugging policies.

  ## Commands

  - `c`, `continue` - Continue execution until next breakpoint
  - `s`, `step` - Step into next statement
  - `n`, `next` - Step over next statement
  - `f`, `finish` - Finish current function
  - `b <target>` - Set breakpoint (policy name or line number)
  - `d <num>` - Delete breakpoint by number
  - `l` - List all breakpoints
  - `p <var>` - Print variable value
  - `vars` - List all variables
  - `stack` - Show call stack
  - `trace` - Show execution trace
  - `w <expr>` - Add watch expression
  - `watches` - Show all watches
  - `help` - Show help
  - `quit` - Exit debugger
  """

  alias Phronesis.Debugger

  @commands %{
    "c" => :continue,
    "continue" => :continue,
    "s" => :step,
    "step" => :step,
    "n" => :next,
    "next" => :next,
    "f" => :finish,
    "finish" => :finish,
    "b" => :break,
    "break" => :break,
    "d" => :delete,
    "delete" => :delete,
    "l" => :list,
    "list" => :list,
    "p" => :print,
    "print" => :print,
    "vars" => :vars,
    "variables" => :vars,
    "stack" => :stack,
    "trace" => :trace,
    "w" => :watch,
    "watch" => :watch,
    "watches" => :watches,
    "help" => :help,
    "h" => :help,
    "?" => :help,
    "quit" => :quit,
    "q" => :quit,
    "exit" => :quit
  }

  @doc """
  Start the debugger REPL for a policy file.
  """
  def start(file_path, opts \\ []) do
    case Debugger.start(file_path) do
      {:ok, session} ->
        IO.puts("Phronesis Debugger v0.2.0")
        IO.puts("Type 'help' for commands, 'quit' to exit")
        IO.puts("")

        # Load initial context if provided
        session =
          if context = opts[:context] do
            Debugger.load_context(session, context)
          else
            session
          end

        # Set initial breakpoints if provided
        session =
          Enum.reduce(opts[:breakpoints] || [], session, fn bp, sess ->
            Debugger.set_breakpoint(sess, bp)
          end)

        IO.puts(Debugger.format_state(session))
        IO.puts("")

        repl_loop(session)

      {:error, reason} ->
        IO.puts("Error loading file: #{inspect(reason)}")
        {:error, reason}
    end
  end

  ## REPL Loop

  defp repl_loop(session) do
    prompt = build_prompt(session)
    input = IO.gets(prompt) |> String.trim()

    case parse_command(input) do
      {:ok, :quit} ->
        IO.puts("Exiting debugger")
        :ok

      {:ok, command, args} ->
        case handle_command(command, args, session) do
          {:ok, new_session} ->
            repl_loop(new_session)

          {:break, new_session, node} ->
            IO.puts("\nBreakpoint hit: #{format_node(node)}")
            IO.puts(Debugger.format_state(new_session))
            repl_loop(new_session)

          {:done, new_session} ->
            IO.puts("\nExecution complete")
            IO.puts("Final state:")
            IO.inspect(new_session.state, pretty: true)
            repl_loop(new_session)

          {:error, reason} ->
            IO.puts("Error: #{inspect(reason)}")
            repl_loop(session)
        end

      {:error, reason} ->
        IO.puts("Invalid command: #{reason}")
        IO.puts("Type 'help' for available commands")
        repl_loop(session)
    end
  end

  defp build_prompt(session) do
    pos =
      case session.current_position do
        nil -> "start"
        {:policy, name, _, _, _} -> "#{name}"
        _ -> "exec"
      end

    "(pdb:#{pos}) "
  end

  defp parse_command(input) do
    parts = String.split(input, " ", parts: 2)

    case parts do
      [cmd] ->
        case Map.fetch(@commands, cmd) do
          {:ok, command} -> {:ok, command, []}
          :error -> {:error, "unknown command: #{cmd}"}
        end

      [cmd, args] ->
        case Map.fetch(@commands, cmd) do
          {:ok, command} -> {:ok, command, [args]}
          :error -> {:error, "unknown command: #{cmd}"}
        end
    end
  end

  ## Command Handlers

  defp handle_command(:continue, _args, session) do
    IO.puts("Continuing execution...")
    Debugger.continue(session)
  end

  defp handle_command(:step, _args, session) do
    IO.puts("Stepping into...")
    Debugger.step(session)
  end

  defp handle_command(:next, _args, session) do
    IO.puts("Stepping over...")
    Debugger.next(session)
  end

  defp handle_command(:finish, _args, session) do
    IO.puts("Finishing current scope...")
    Debugger.finish(session)
  end

  defp handle_command(:break, [target], session) do
    breakpoint =
      cond do
        String.match?(target, ~r/^\d+$/) ->
          [line: String.to_integer(target)]

        true ->
          [policy: target]
      end

    new_session = Debugger.set_breakpoint(session, breakpoint)
    IO.puts("Breakpoint set: #{inspect(breakpoint)}")
    {:ok, new_session}
  end

  defp handle_command(:break, [], _session) do
    {:error, "Usage: b <policy_name|line_number>"}
  end

  defp handle_command(:delete, [num_str], session) do
    case Integer.parse(num_str) do
      {num, ""} ->
        breakpoints = Debugger.list_breakpoints(session)

        case Enum.at(breakpoints, num) do
          nil ->
            {:error, "No breakpoint ##{num}"}

          bp ->
            new_session = Debugger.remove_breakpoint(session, bp)
            IO.puts("Deleted breakpoint ##{num}: #{inspect(bp)}")
            {:ok, new_session}
        end

      _ ->
        {:error, "Invalid breakpoint number"}
    end
  end

  defp handle_command(:delete, [], _session) do
    {:error, "Usage: d <breakpoint_number>"}
  end

  defp handle_command(:list, _args, session) do
    breakpoints = Debugger.list_breakpoints(session)

    if Enum.empty?(breakpoints) do
      IO.puts("No breakpoints set")
    else
      IO.puts("Breakpoints:")

      breakpoints
      |> Enum.with_index()
      |> Enum.each(fn {bp, idx} ->
        IO.puts("  #{idx}. #{format_breakpoint(bp)}")
      end)
    end

    {:ok, session}
  end

  defp handle_command(:print, [var_name], session) do
    case Debugger.inspect_var(session, var_name) do
      {:ok, value} ->
        IO.puts("#{var_name} = #{inspect(value, pretty: true)}")

      {:error, :not_found} ->
        IO.puts("Variable '#{var_name}' not found")
    end

    {:ok, session}
  end

  defp handle_command(:print, [], _session) do
    {:error, "Usage: p <variable_name>"}
  end

  defp handle_command(:vars, _args, session) do
    vars = Debugger.list_vars(session)

    if map_size(vars) == 0 do
      IO.puts("No variables in scope")
    else
      IO.puts("Variables:")

      Enum.each(vars, fn {name, value} ->
        IO.puts("  #{name} = #{inspect(value, pretty: true, limit: 3)}")
      end)
    end

    {:ok, session}
  end

  defp handle_command(:stack, _args, session) do
    stack = Debugger.show_stack(session)

    if Enum.empty?(stack) do
      IO.puts("Empty call stack")
    else
      IO.puts("Call Stack:")

      stack
      |> Enum.with_index()
      |> Enum.each(fn {frame, idx} ->
        IO.puts("  #{idx}. #{format_node(frame)}")
      end)
    end

    {:ok, session}
  end

  defp handle_command(:trace, _args, session) do
    trace_output = Debugger.show_trace(session)
    IO.puts("Execution Trace:")
    IO.puts(trace_output)
    {:ok, session}
  end

  defp handle_command(:watch, [expr], session) do
    new_session = Debugger.add_watch(session, expr, expr)
    IO.puts("Watch added: #{expr}")
    {:ok, new_session}
  end

  defp handle_command(:watch, [], _session) do
    {:error, "Usage: w <expression>"}
  end

  defp handle_command(:watches, _args, session) do
    watches = Debugger.eval_watches(session)

    if Enum.empty?(watches) do
      IO.puts("No watches set")
    else
      IO.puts("Watches:")

      Enum.each(watches, fn {name, value} ->
        IO.puts("  #{name} = #{inspect(value, pretty: true)}")
      end)
    end

    {:ok, session}
  end

  defp handle_command(:help, _args, session) do
    IO.puts("""
    Phronesis Debugger Commands:

    Execution Control:
      c, continue      Continue execution until next breakpoint
      s, step          Step into next statement
      n, next          Step over next statement
      f, finish        Finish current function

    Breakpoints:
      b <target>       Set breakpoint (policy name or line number)
      d <num>          Delete breakpoint by number
      l, list          List all breakpoints

    Inspection:
      p <var>          Print variable value
      vars             List all variables
      stack            Show call stack
      trace            Show execution trace
      w <expr>         Add watch expression
      watches          Show all watches

    Other:
      help, h, ?       Show this help
      quit, q, exit    Exit debugger

    Examples:
      b validate_route     Set breakpoint on policy
      b 42                 Set breakpoint on line 42
      p route              Print 'route' variable
      w status             Watch 'status' variable
    """)

    {:ok, session}
  end

  ## Formatting Helpers

  defp format_node({:policy, name, _cond, _action, meta}) do
    "POLICY #{name} (line #{meta[:line] || "?"})"
  end

  defp format_node({:const, name, _value, meta}) do
    "CONST #{name} = ... (line #{meta[:line] || "?"})"
  end

  defp format_node(node) do
    inspect(node, pretty: false, limit: 20)
  end

  defp format_breakpoint({:policy, name}), do: "policy: #{name}"
  defp format_breakpoint({:line, num}), do: "line: #{num}"
  defp format_breakpoint({:condition, cond}), do: "condition: #{inspect(cond)}"
end
