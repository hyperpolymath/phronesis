# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.CLI do
  @moduledoc """
  Command-line interface for the Phronesis policy language.

  ## Usage

      # Run a policy file
      phronesis run policy.phr

      # Parse and show AST
      phronesis parse policy.phr

      # Validate syntax only
      phronesis check policy.phr

      # Compile to bytecode
      phronesis compile policy.phr -o policy.phrc

      # Run compiled bytecode
      phronesis run policy.phrc

      # Disassemble bytecode
      phronesis disasm policy.phrc

      # Start interactive REPL
      phronesis repl

      # Show version
      phronesis --version
  """

  alias Phronesis.{State, Interpreter, Compiler, Formatter, Linter}

  @version Mix.Project.config()[:version]

  def main(args) do
    args
    |> parse_args()
    |> run()
  end

  defp parse_args(args) do
    {opts, args, _} =
      OptionParser.parse(args,
        switches: [
          help: :boolean,
          version: :boolean,
          verbose: :boolean,
          output: :string,
          optimize: :boolean,
          env: :string
        ],
        aliases: [h: :help, v: :version, V: :verbose, o: :output, O: :optimize, e: :env]
      )

    {opts, args}
  end

  defp run({opts, args}) do
    cond do
      opts[:version] ->
        IO.puts("Phronesis #{@version}")

      opts[:help] ->
        IO.puts(@moduledoc)

      args == ["repl"] ->
        repl()

      match?(["run", _], args) ->
        ["run", file] = args
        run_file(file)

      match?(["parse", _], args) ->
        ["parse", file] = args
        parse_file(file)

      match?(["check", _], args) ->
        ["check", file] = args
        check_file(file)

      match?(["compile", _], args) ->
        ["compile", file] = args
        compile_file(file, opts)

      match?(["disasm", _], args) ->
        ["disasm", file] = args
        disasm_file(file)

      match?(["fmt" | _], args) ->
        ["fmt" | files] = args
        format_files(files, opts)

      match?(["lint" | _], args) ->
        ["lint" | files] = args
        lint_files(files, opts)

      args == [] ->
        show_usage()

      true ->
        [cmd | _] = args
        IO.puts(:stderr, "Unknown command: #{cmd}")
        IO.puts(:stderr, "Run 'phronesis --help' for usage")
        System.halt(1)
    end
  end

  defp show_usage do
    IO.puts("Phronesis #{@version} - Network Policy Language")
    IO.puts("")
    IO.puts("Usage: phronesis <command> [options] [file]")
    IO.puts("")
    IO.puts("Commands:")
    IO.puts("  run <file>        Execute a policy file (.phr or .phrc)")
    IO.puts("  parse <file>      Parse and display AST")
    IO.puts("  check <file>      Validate syntax only")
    IO.puts("  compile <file>    Compile to bytecode (.phrc)")
    IO.puts("  disasm <file>     Disassemble bytecode")
    IO.puts("  repl              Start interactive REPL")
    IO.puts("")
    IO.puts("Options:")
    IO.puts("  -h, --help        Show this help")
    IO.puts("  -v, --version     Show version")
    IO.puts("  -V, --verbose     Verbose output")
    IO.puts("  -o, --output      Output file for compile")
    IO.puts("  -O, --optimize    Enable optimizations (default: true)")
  end

  # REPL implementation
  defp repl do
    IO.puts("Phronesis #{@version} REPL")
    IO.puts("Type :help for commands, :quit to exit")
    IO.puts("")

    state = State.new()
    repl_loop(state)
  end

  defp repl_loop(state) do
    case IO.gets("phronesis> ") do
      :eof ->
        IO.puts("\nBye!")

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{inspect(reason)}")
        repl_loop(state)

      line ->
        line = String.trim(line)
        {state, continue?} = handle_repl_input(line, state)

        if continue? do
          repl_loop(state)
        else
          IO.puts("Bye!")
        end
    end
  end

  defp handle_repl_input("", state), do: {state, true}
  defp handle_repl_input(":quit", state), do: {state, false}
  defp handle_repl_input(":exit", state), do: {state, false}
  defp handle_repl_input(":q", state), do: {state, false}

  defp handle_repl_input(":help", state) do
    IO.puts("""
    Commands:
      :help          Show this help
      :quit          Exit REPL
      :state         Show current state
      :policies      List registered policies
      :env           Show environment variables
      :clear         Clear state
      :load <file>   Load a policy file

    Or enter Phronesis code directly:
      CONST x = 42
      POLICY test: x > 10 THEN ACCEPT() PRIORITY: 1
    """)

    {state, true}
  end

  defp handle_repl_input(":state", state) do
    IO.puts("Policies: #{map_size(state.policy_table)}")
    IO.puts("Environment: #{map_size(state.environment)} bindings")
    IO.puts("Consensus log: #{length(state.consensus_log)} entries")
    IO.puts("Agents: #{inspect(state.agents)}")
    IO.puts("Threshold: #{state.consensus_threshold}")
    {state, true}
  end

  defp handle_repl_input(":policies", state) do
    if map_size(state.policy_table) == 0 do
      IO.puts("No policies registered")
    else
      state.policy_table
      |> Enum.each(fn {name, {:policy, _, _, _, %{priority: p}}} ->
        IO.puts("  #{name} (priority: #{p})")
      end)
    end

    {state, true}
  end

  defp handle_repl_input(":env", state) do
    if map_size(state.environment) == 0 do
      IO.puts("Environment is empty")
    else
      state.environment
      |> Enum.each(fn {k, v} ->
        IO.puts("  #{k} = #{inspect(v)}")
      end)
    end

    {state, true}
  end

  defp handle_repl_input(":clear", _state) do
    IO.puts("State cleared")
    {State.new(), true}
  end

  defp handle_repl_input(":load " <> file, state) do
    case load_and_execute(String.trim(file), state) do
      {:ok, new_state} ->
        IO.puts("Loaded: #{file}")
        {new_state, true}

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{format_error(reason)}")
        {state, true}
    end
  end

  defp handle_repl_input(":" <> cmd, state) do
    IO.puts(:stderr, "Unknown command: :#{cmd}")
    {state, true}
  end

  defp handle_repl_input(input, state) do
    case Phronesis.parse(input) do
      {:ok, ast} ->
        case Interpreter.execute(ast, state) do
          {:ok, new_state} ->
            # Show what was added
            show_execution_result(state, new_state, ast)
            {new_state, true}

          {:error, reason} ->
            IO.puts(:stderr, "Execution error: #{format_error(reason)}")
            {state, true}
        end

      {:error, reason} ->
        IO.puts(:stderr, "Parse error: #{format_error(reason)}")
        {state, true}
    end
  end

  defp show_execution_result(_old_state, new_state, ast) do
    Enum.each(ast, fn
      {:const, name, _} ->
        {:ok, value} = State.lookup(new_state, name)
        IO.puts("#{name} = #{inspect(value)}")

      {:policy, name, _, _, %{priority: p}} ->
        IO.puts("Policy '#{name}' registered (priority: #{p})")

      {:import, path, nil} ->
        IO.puts("Imported #{Enum.join(path, ".")}")

      {:import, path, alias_name} ->
        IO.puts("Imported #{Enum.join(path, ".")} as #{alias_name}")
    end)
  end

  # File operations

  defp run_file(path) do
    state = State.new()

    case load_and_execute(path, state) do
      {:ok, final_state} ->
        IO.puts("Executed: #{path}")
        IO.puts("Policies registered: #{map_size(final_state.policy_table)}")

        if length(final_state.consensus_log) > 0 do
          IO.puts("Actions executed: #{length(final_state.consensus_log)}")
        end

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{format_error(reason)}")
        System.halt(1)
    end
  end

  defp parse_file(path) do
    case File.read(path) do
      {:ok, source} ->
        case Phronesis.parse(source) do
          {:ok, ast} ->
            IO.puts("# AST for #{path}")
            IO.puts(inspect(ast, pretty: true, limit: :infinity))

          {:error, reason} ->
            IO.puts(:stderr, "Parse error: #{format_error(reason)}")
            System.halt(1)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Cannot read #{path}: #{reason}")
        System.halt(1)
    end
  end

  defp check_file(path) do
    case File.read(path) do
      {:ok, source} ->
        case Phronesis.parse(source) do
          {:ok, ast} ->
            IO.puts("✓ #{path} is valid")
            IO.puts("  #{length(ast)} declaration(s)")

          {:error, reason} ->
            IO.puts("✗ #{path} has errors:")
            IO.puts("  #{format_error(reason)}")
            System.halt(1)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Cannot read #{path}: #{reason}")
        System.halt(1)
    end
  end

  defp compile_file(path, opts) do
    output = opts[:output] || String.replace(path, ~r/\.phr$/, ".phrc")
    optimize = Keyword.get(opts, :optimize, true)

    case File.read(path) do
      {:ok, source} ->
        case Compiler.compile(source, optimize: optimize) do
          {:ok, bytecode} ->
            case Compiler.save(bytecode, output) do
              :ok ->
                IO.puts("Compiled: #{path} -> #{output}")
                IO.puts("  #{length(bytecode.instructions)} instructions")
                IO.puts("  #{map_size(bytecode.constants)} constants")
                IO.puts("  #{length(bytecode.policies)} policies")

              {:error, reason} ->
                IO.puts(:stderr, "Cannot write #{output}: #{reason}")
                System.halt(1)
            end

          {:error, reason} ->
            IO.puts(:stderr, "Compile error: #{format_error(reason)}")
            System.halt(1)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Cannot read #{path}: #{reason}")
        System.halt(1)
    end
  end

  defp disasm_file(path) do
    case Compiler.load(path) do
      {:ok, bytecode} ->
        IO.puts("# Disassembly of #{path}")
        IO.puts(Compiler.disassemble(bytecode))

      {:error, reason} ->
        IO.puts(:stderr, "Cannot load #{path}: #{format_error(reason)}")
        System.halt(1)
    end
  end

  defp format_files([], _opts) do
    IO.puts(:stderr, "Usage: phronesis fmt <file>...")
    System.halt(1)
  end

  defp format_files(files, opts) do
    check_only = Keyword.get(opts, :check, false)

    results = Enum.map(files, fn file ->
      case File.read(file) do
        {:ok, source} ->
          if check_only do
            case Formatter.check(source) do
              :ok -> {:ok, file, :unchanged}
              {:error, :not_formatted} -> {:error, file, :needs_formatting}
              {:error, reason} -> {:error, file, reason}
            end
          else
            case Formatter.format(source) do
              {:ok, formatted} ->
                if formatted == source do
                  {:ok, file, :unchanged}
                else
                  case File.write(file, formatted) do
                    :ok -> {:ok, file, :formatted}
                    {:error, reason} -> {:error, file, reason}
                  end
                end

              {:error, reason} ->
                {:error, file, reason}
            end
          end

        {:error, reason} ->
          {:error, file, reason}
      end
    end)

    errors = Enum.filter(results, &match?({:error, _, _}, &1))
    formatted = Enum.filter(results, &match?({:ok, _, :formatted}, &1))
    needs_fmt = Enum.filter(results, &match?({:error, _, :needs_formatting}, &1))

    if check_only do
      if needs_fmt != [] do
        IO.puts("Files need formatting:")
        Enum.each(needs_fmt, fn {:error, f, _} -> IO.puts("  #{f}") end)
        System.halt(1)
      else
        IO.puts("All files are formatted correctly.")
      end
    else
      if formatted != [] do
        IO.puts("Formatted #{length(formatted)} file(s):")
        Enum.each(formatted, fn {:ok, f, _} -> IO.puts("  #{f}") end)
      end
    end

    if errors != [] do
      IO.puts(:stderr, "Errors:")
      Enum.each(errors, fn {:error, f, reason} ->
        IO.puts(:stderr, "  #{f}: #{format_error(reason)}")
      end)
      System.halt(1)
    end
  end

  defp lint_files([], _opts) do
    IO.puts(:stderr, "Usage: phronesis lint <file>...")
    System.halt(1)
  end

  defp lint_files(files, _opts) do
    all_issues = Enum.flat_map(files, fn file ->
      case Linter.lint_file(file) do
        {:ok, issues} ->
          Enum.map(issues, fn issue -> Map.put(issue, :file, file) end)

        {:error, reason} ->
          IO.puts(:stderr, "#{file}: #{format_error(reason)}")
          []
      end
    end)

    if all_issues == [] do
      IO.puts("No issues found in #{length(files)} file(s).")
    else
      grouped = Enum.group_by(all_issues, & &1.file)

      Enum.each(grouped, fn {file, issues} ->
        IO.puts("\n#{file}:")
        Enum.each(issues, fn issue ->
          severity = format_lint_severity(issue.severity)
          IO.puts("  #{issue.line}:#{issue.column}: #{severity} [#{issue.code}] #{issue.message}")
          if issue.suggestion do
            IO.puts("    Suggestion: #{issue.suggestion}")
          end
        end)
      end)

      errors = Enum.count(all_issues, & &1.severity == :error)
      warnings = Enum.count(all_issues, & &1.severity == :warning)
      infos = Enum.count(all_issues, & &1.severity == :info)

      IO.puts("\nSummary: #{errors} error(s), #{warnings} warning(s), #{infos} info(s)")

      if errors > 0, do: System.halt(1)
    end
  end

  defp format_lint_severity(:error), do: "error"
  defp format_lint_severity(:warning), do: "warning"
  defp format_lint_severity(:info), do: "info"

  defp load_and_execute(path, state) do
    with {:ok, source} <- File.read(path),
         {:ok, ast} <- Phronesis.parse(source),
         {:ok, new_state} <- Interpreter.execute(ast, state) do
      {:ok, new_state}
    end
  end

  defp format_error({:parse_error, msg, line, col}) do
    "#{msg} at line #{line}, column #{col}"
  end

  defp format_error({:lexer_error, msg, line, col}) do
    "#{msg} at line #{line}, column #{col}"
  end

  defp format_error({:file_error, reason}) do
    "file error: #{reason}"
  end

  defp format_error(other) do
    inspect(other)
  end
end
