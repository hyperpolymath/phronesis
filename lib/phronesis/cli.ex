# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
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

      # Start interactive REPL
      phronesis repl

      # Show version
      phronesis --version
  """

  alias Phronesis.{State, Interpreter}
  alias Phronesis.Diagnostics.Reporter

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
          env: :string,
          output: :string
        ],
        aliases: [h: :help, v: :version, V: :verbose, e: :env, o: :output]
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
        format = Keyword.get(opts, :output, "debug")
        parse_file(file, format)

      match?(["dump-sexpr", _], args) ->
        ["dump-sexpr", file] = args
        parse_file(file, "sexpr")

      match?(["check", _], args) ->
        ["check", file] = args
        check_file(file)

      match?(["diagnose", _], args) ->
        ["diagnose", file] = args
        diagnose_file(file, opts)

      match?(["test", _], args) ->
        ["test", file] = args
        test_file(file, opts)

      args == ["lsp"] ->
        start_lsp_server()

      match?(["debug", _], args) ->
        ["debug", file] = args
        debug_file(file, opts)

      match?(["profile", _], args) ->
        ["profile", file] = args
        profile_file(file, opts)

      match?(["docs", _], args) ->
        ["docs", path] = args
        generate_docs(path, opts)

      match?(["analyze", _], args) ->
        ["analyze", path] = args
        analyze_file_or_project(path, opts)

      match?(["pkg" | _], args) ->
        handle_pkg_command(tl(args), opts)

      args == ["benchmark"] ->
        run_benchmarks(opts)

      match?(["benchmark", _], args) ->
        ["benchmark", name] = args
        run_benchmark(name, opts)

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
    IO.puts("  run <file>     Execute a policy file")
    IO.puts("  parse <file>   Parse and display AST (--output debug|sexpr|json)")
    IO.puts("  dump-sexpr <file> Parse and dump AST as S-expression")
    IO.puts("  check <file>   Validate syntax only")
    IO.puts("  diagnose <file> Enhanced error reporting with suggestions")
    IO.puts("  test <file>    Run policy tests")
    IO.puts("  debug <file>   Start interactive debugger")
    IO.puts("  profile <file> Profile policy performance")
    IO.puts("  analyze <path> Static code analysis")
    IO.puts("  docs <path>    Generate documentation")
    IO.puts("  benchmark [name] Run performance benchmarks")
    IO.puts("  lsp            Start Language Server Protocol server")
    IO.puts("  repl           Start interactive REPL")
    IO.puts("  pkg <command>  Package manager commands")
    IO.puts("")
    IO.puts("Options:")
    IO.puts("  -h, --help     Show this help")
    IO.puts("  -v, --version  Show version")
    IO.puts("  -V, --verbose  Verbose output")
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

  # Parse a file and display the AST in the requested output format.
  #
  # Supported formats:
  #   - "debug"  — Elixir inspect pretty-print (default)
  #   - "sexpr"  — S-expression representation following JtV reference pattern
  #   - "json"   — Pretty-printed JSON via Jason
  defp parse_file(path, format \\ "debug") do
    case File.read(path) do
      {:ok, source} ->
        case Phronesis.parse(source) do
          {:ok, ast} ->
            case format do
              "json" ->
                IO.puts(Jason.encode!(ast_to_json(ast), pretty: true))

              "sexpr" ->
                IO.puts(ast_to_sexpr(ast))

              _ ->
                IO.puts("# AST for #{path}")
                IO.puts(inspect(ast, pretty: true, limit: :infinity))
            end

          {:error, reason} ->
            IO.puts(:stderr, "Parse error: #{format_error(reason)}")
            System.halt(1)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Cannot read #{path}: #{reason}")
        System.halt(1)
    end
  end

  # ============================================================================
  # S-expression AST dump
  #
  # Converts the Phronesis AST (list of tagged tuples) into a Lisp-like
  # S-expression representation, following the JtV reference pattern. Each
  # AST node becomes a parenthesised list tagged by its variant name.
  # ============================================================================

  @doc false
  defp ast_to_sexpr(declarations) when is_list(declarations) do
    inner =
      declarations
      |> Enum.map(&decl_to_sexpr(&1, 2))
      |> Enum.join("\n  ")

    "(program\n  #{inner})"
  end

  # Convert a single top-level declaration to S-expression.
  defp decl_to_sexpr(decl, indent) do
    pad = String.duplicate(" ", indent)

    case decl do
      {:const, name, value} ->
        "(const \"#{name}\" #{value_to_sexpr(value)})"

      {:policy, name, condition, action, metadata} ->
        priority = Map.get(metadata, :priority, 0)
        tags = Map.get(metadata, :tags, [])

        tags_sexpr =
          if tags == [],
            do: "",
            else: " (tags#{Enum.map_join(tags, "", &" \"#{&1}\"")})"

        "(policy \"#{name}\" :priority #{priority}#{tags_sexpr}\n" <>
          "#{pad}  (condition #{condition_to_sexpr(condition)})\n" <>
          "#{pad}  (action #{action_to_sexpr(action)}))"

      {:import, path, nil} ->
        "(import \"#{Enum.join(path, ".")}\")"

      {:import, path, alias_name} ->
        "(import \"#{Enum.join(path, ".")}\" :as \"#{alias_name}\")"

      other ->
        "(unknown #{inspect(other)})"
    end
  end

  # Convert a condition expression to S-expression.
  defp condition_to_sexpr(condition) do
    case condition do
      {:comparison, op, left, right} ->
        "(#{op} #{value_to_sexpr(left)} #{value_to_sexpr(right)})"

      {:logical, op, left, right} ->
        "(#{op} #{condition_to_sexpr(left)} #{condition_to_sexpr(right)})"

      {:not, inner} ->
        "(not #{condition_to_sexpr(inner)})"

      {:in, value, list} ->
        "(in #{value_to_sexpr(value)} #{value_to_sexpr(list)})"

      {:between, value, low, high} ->
        "(between #{value_to_sexpr(value)} #{value_to_sexpr(low)} #{value_to_sexpr(high)})"

      {:call, name, args} ->
        args_sexpr = Enum.map_join(args, " ", &value_to_sexpr/1)
        "(call \"#{name}\" #{args_sexpr})"

      {:literal, _type, value} ->
        value_to_sexpr({:literal, nil, value})

      {:identifier, name} ->
        "(ident \"#{name}\")"

      other ->
        inspect(other)
    end
  end

  # Convert an action to S-expression.
  defp action_to_sexpr(action) do
    case action do
      {:call, name, args} ->
        args_sexpr = Enum.map_join(args, " ", &value_to_sexpr/1)
        "(call \"#{name}\"#{if args_sexpr == "", do: "", else: " #{args_sexpr}"})"

      {:block, actions} ->
        inner = Enum.map_join(actions, " ", &action_to_sexpr/1)
        "(block #{inner})"

      other ->
        inspect(other)
    end
  end

  # Convert a value/literal to S-expression.
  defp value_to_sexpr(value) do
    case value do
      {:literal, :integer, v} -> "(int #{v})"
      {:literal, :float, v} -> "(float #{v})"
      {:literal, :string, v} -> "(string #{inspect(v)})"
      {:literal, :boolean, v} -> "(bool #{v})"
      {:literal, _, v} -> inspect(v)
      {:identifier, name} -> "(ident \"#{name}\")"
      {:field_access, obj, field} -> "(field-access #{value_to_sexpr(obj)} \"#{field}\")"
      {:call, name, args} ->
        args_sexpr = Enum.map_join(args, " ", &value_to_sexpr/1)
        "(call \"#{name}\" #{args_sexpr})"
      {:list, items} ->
        inner = Enum.map_join(items, " ", &value_to_sexpr/1)
        "(list #{inner})"
      {:map, pairs} ->
        inner =
          Enum.map_join(pairs, " ", fn {k, v} ->
            "(#{value_to_sexpr(k)} #{value_to_sexpr(v)})"
          end)
        "(map #{inner})"
      {:binary_op, op, left, right} ->
        "(#{op} #{value_to_sexpr(left)} #{value_to_sexpr(right)})"
      {:unary_op, op, operand} ->
        "(#{op} #{value_to_sexpr(operand)})"
      other when is_binary(other) -> inspect(other)
      other when is_number(other) -> "#{other}"
      other when is_atom(other) -> "#{other}"
      other -> inspect(other)
    end
  end

  # ============================================================================
  # JSON AST dump
  #
  # Converts the Phronesis AST to a JSON-serialisable map structure so that
  # Jason can pretty-print it. Each declaration becomes a map with a "type"
  # field discriminating the variant.
  # ============================================================================

  @doc false
  defp ast_to_json(declarations) when is_list(declarations) do
    %{"program" => Enum.map(declarations, &decl_to_json/1)}
  end

  defp decl_to_json(decl) do
    case decl do
      {:const, name, value} ->
        %{"type" => "const", "name" => name, "value" => value_to_json(value)}

      {:policy, name, condition, action, metadata} ->
        %{
          "type" => "policy",
          "name" => name,
          "priority" => Map.get(metadata, :priority, 0),
          "tags" => Map.get(metadata, :tags, []),
          "condition" => condition_to_json(condition),
          "action" => action_to_json(action)
        }

      {:import, path, alias_name} ->
        base = %{"type" => "import", "path" => Enum.join(path, ".")}
        if alias_name, do: Map.put(base, "alias", alias_name), else: base

      other ->
        %{"type" => "unknown", "raw" => inspect(other)}
    end
  end

  defp condition_to_json(condition) do
    case condition do
      {:comparison, op, left, right} ->
        %{"type" => "comparison", "op" => to_string(op),
          "left" => value_to_json(left), "right" => value_to_json(right)}

      {:logical, op, left, right} ->
        %{"type" => "logical", "op" => to_string(op),
          "left" => condition_to_json(left), "right" => condition_to_json(right)}

      {:not, inner} ->
        %{"type" => "not", "operand" => condition_to_json(inner)}

      {:identifier, name} ->
        %{"type" => "identifier", "name" => name}

      {:literal, type, value} ->
        %{"type" => "literal", "kind" => to_string(type), "value" => value}

      other ->
        %{"type" => "unknown", "raw" => inspect(other)}
    end
  end

  defp action_to_json(action) do
    case action do
      {:call, name, args} ->
        %{"type" => "call", "name" => name, "args" => Enum.map(args, &value_to_json/1)}

      {:block, actions} ->
        %{"type" => "block", "actions" => Enum.map(actions, &action_to_json/1)}

      other ->
        %{"type" => "unknown", "raw" => inspect(other)}
    end
  end

  defp value_to_json(value) do
    case value do
      {:literal, type, v} ->
        %{"type" => "literal", "kind" => to_string(type), "value" => v}

      {:identifier, name} ->
        %{"type" => "identifier", "name" => name}

      {:field_access, obj, field} ->
        %{"type" => "field_access", "object" => value_to_json(obj), "field" => field}

      {:call, name, args} ->
        %{"type" => "call", "name" => name, "args" => Enum.map(args, &value_to_json/1)}

      {:list, items} ->
        %{"type" => "list", "items" => Enum.map(items, &value_to_json/1)}

      {:binary_op, op, left, right} ->
        %{"type" => "binary_op", "op" => to_string(op),
          "left" => value_to_json(left), "right" => value_to_json(right)}

      {:unary_op, op, operand} ->
        %{"type" => "unary_op", "op" => to_string(op), "operand" => value_to_json(operand)}

      other when is_binary(other) -> other
      other when is_number(other) -> other
      other when is_atom(other) -> to_string(other)
      other -> inspect(other)
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

  defp diagnose_file(path, opts) do
    use_color = Keyword.get(opts, :color, true)
    format = Keyword.get(opts, :format, :text)

    case File.read(path) do
      {:ok, source} ->
        source_lines = String.split(source, "\n")
        report = Reporter.new(path)

        # Try to parse and collect diagnostics
        report =
          case Phronesis.Lexer.tokenize(source) do
            {:ok, _tokens} ->
              # Lexer succeeded, try parser
              case Phronesis.parse(source) do
                {:ok, ast} ->
                  # Syntax is valid, run static analysis
                  case Phronesis.Analyzer.analyze_file(path, severity: :info) do
                    {:ok, issues} ->
                      Reporter.from_analyzer_issues(path, issues)

                    {:error, _} ->
                      report
                  end

                {:error, {:parse_error, message, line, column, _meta}} ->
                  context = Enum.at(source_lines, line - 1, "")

                  diagnostic =
                    Phronesis.Diagnostics.parser_error(message, path, line, column,
                      context: context
                    )

                  Reporter.add(report, diagnostic)

                {:error, {:parser_error, message, line, column}} ->
                  context = Enum.at(source_lines, line - 1, "")

                  diagnostic =
                    Phronesis.Diagnostics.parser_error(message, path, line, column,
                      context: context
                    )

                  Reporter.add(report, diagnostic)

                {:error, reason} ->
                  IO.puts(:stderr, "Parse error: #{inspect(reason)}")
                  report
              end

            {:error, errors} ->
              # Lexer errors
              Reporter.from_lexer_errors(path, errors, source_lines)
          end

        # Format and display the report
        output =
          case format do
            :json -> Reporter.to_json(report)
            :text -> Reporter.to_text(report)
            _ -> Reporter.format(report, color: use_color)
          end

        IO.puts(output)

        # Exit with appropriate code
        if Reporter.has_errors?(report) do
          System.halt(1)
        else
          System.halt(0)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Cannot read #{path}: #{reason}")
        System.halt(1)
    end
  end

  defp test_file(path, opts) do
    verbose = Keyword.get(opts, :verbose, true)

    case Phronesis.TestFramework.run_file(path, verbose: verbose) do
      {:ok, results} ->
        # Count results
        passed = Enum.count(results, &match?({:pass, _, _}, &1))
        failed = Enum.count(results, &match?({:fail, _, _, _}, &1))
        errors = Enum.count(results, &match?({:error, _, _, _}, &1))

        if failed == 0 and errors == 0 do
          IO.puts("\n✓ All #{passed} tests passed")
          System.halt(0)
        else
          IO.puts("\n✗ #{failed} failed, #{errors} errors, #{passed} passed")
          System.halt(1)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Test error: #{format_error(reason)}")
        System.halt(1)
    end
  end

  defp debug_file(path, _opts) do
    Phronesis.Debugger.REPL.start(path)
  end

  defp profile_file(path, opts) do
    interactive = Keyword.get(opts, :verbose, false)

    case Phronesis.Profiler.start(path) do
      {:ok, session} ->
        case Phronesis.Profiler.run(session) do
          {:ok, profiled_session} ->
            if interactive do
              Phronesis.Profiler.Reporter.interactive(profiled_session)
            else
              report = Phronesis.Profiler.format_report(profiled_session)
              IO.puts(report)
            end

          {:error, reason} ->
            IO.puts(:stderr, "Profiling error: #{inspect(reason)}")
            System.halt(1)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{format_error(reason)}")
        System.halt(1)
    end
  end

  defp generate_docs(path, opts) do
    output_dir = Keyword.get(opts, :output, "docs")
    format = Keyword.get(opts, :format, "html")

    IO.puts("Generating documentation for: #{path}")

    result =
      if File.dir?(path) do
        # Generate project docs
        project_opts = [
          name: Keyword.get(opts, :name, Path.basename(path)),
          version: Keyword.get(opts, :version, "0.1.0")
        ]

        Phronesis.DocGenerator.generate_project(path, project_opts)
      else
        # Generate single file docs
        Phronesis.DocGenerator.generate_file(path)
      end

    case result do
      {:ok, docs} ->
        case format do
          "html" ->
            {:ok, output_path} = Phronesis.DocGenerator.export_html(docs, output_dir)
            IO.puts("✓ HTML documentation generated in: #{output_path}")
            IO.puts("  Open: #{Path.join(output_path, "index.html")}")

          "markdown" ->
            {:ok, output_path} = Phronesis.DocGenerator.export_markdown(docs, output_dir)
            IO.puts("✓ Markdown documentation generated in: #{output_path}")

          _ ->
            IO.puts(:stderr, "Unknown format: #{format}")
            IO.puts(:stderr, "Supported formats: html, markdown")
            System.halt(1)
        end

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{format_error(reason)}")
        System.halt(1)
    end
  end

  defp analyze_file_or_project(path, opts) do
    severity = Keyword.get(opts, :severity, :info)

    result =
      if File.dir?(path) do
        Phronesis.Analyzer.analyze_project(path, severity: severity)
      else
        Phronesis.Analyzer.analyze_file(path, severity: severity)
      end

    case result do
      {:ok, results} ->
        output = Phronesis.Analyzer.format_results(results)
        IO.puts(output)

        # Exit with error if there are errors
        has_errors =
          if is_list(results) do
            Enum.any?(results, &(&1.stats.errors > 0))
          else
            results.stats.errors > 0
          end

        if has_errors, do: System.halt(1), else: System.halt(0)

      {:error, reason} ->
        IO.puts(:stderr, "Analysis error: #{format_error(reason)}")
        System.halt(1)
    end
  end

  defp handle_pkg_command([], _opts) do
    show_pkg_usage()
  end

  defp handle_pkg_command(["init" | args], opts) do
    name = List.first(args) || Path.basename(File.cwd!())
    version = Keyword.get(opts, :version, "0.1.0")

    case Phronesis.PackageManager.init(name, version: version) do
      {:ok, _manifest} ->
        System.halt(0)

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{inspect(reason)}")
        System.halt(1)
    end
  end

  defp handle_pkg_command(["install", package], opts) do
    case Phronesis.PackageManager.install(package, verbose: true) do
      {:ok, _resolved} ->
        System.halt(0)

      {:error, reason} ->
        IO.puts(:stderr, "Install failed: #{format_error(reason)}")
        System.halt(1)
    end
  end

  defp handle_pkg_command(["list"], _opts) do
    case Phronesis.PackageManager.list() do
      {:ok, packages} ->
        IO.puts(Phronesis.PackageManager.format_list(packages))
        System.halt(0)

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{inspect(reason)}")
        System.halt(1)
    end
  end

  defp handle_pkg_command(["show", package], _opts) do
    case Phronesis.PackageManager.show(package) do
      {:ok, manifest} ->
        IO.puts(Phronesis.PackageManager.format_info(manifest))
        System.halt(0)

      {:error, {:package_not_found, name}} ->
        IO.puts(:stderr, "Package not found: #{name}")
        System.halt(1)

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{inspect(reason)}")
        System.halt(1)
    end
  end

  defp handle_pkg_command([cmd | _], _opts) do
    IO.puts(:stderr, "Unknown pkg command: #{cmd}")
    show_pkg_usage()
    System.halt(1)
  end

  defp show_pkg_usage do
    IO.puts("Package Manager Commands:")
    IO.puts("")
    IO.puts("  phronesis pkg init [name]      Initialize a new package")
    IO.puts("  phronesis pkg install <pkg>    Install a package")
    IO.puts("  phronesis pkg list             List installed packages")
    IO.puts("  phronesis pkg show <pkg>       Show package information")
  end

  defp run_benchmarks(_opts) do
    {:ok, _results} = Phronesis.Benchmark.run_all()
    System.halt(0)
  end

  defp run_benchmark(name, opts) do
    benchmark = String.to_existing_atom(name)
    iterations = Keyword.get(opts, :iterations, 10_000)

    result = Phronesis.Benchmark.run(benchmark, iterations: iterations)

    status = if result.meets_target, do: "✓", else: "✗"
    percentage = (result.throughput / result.target_throughput * 100) |> Float.round(1)

    IO.puts("\n#{status} #{result.name} Benchmark")
    IO.puts("  Throughput: #{format_throughput(result.throughput)} ops/sec (#{percentage}% of target)")
    IO.puts("  Latency:    #{Float.round(result.latency_us, 2)} μs/op")
    IO.puts("  Time:       #{Float.round(result.total_time_ms, 2)} ms (#{result.iterations} iterations)\n")

    if result.meets_target do
      System.halt(0)
    else
      System.halt(1)
    end
  end

  defp format_throughput(num) when num >= 1_000_000 do
    "#{Float.round(num / 1_000_000, 2)}M"
  end

  defp format_throughput(num) when num >= 1_000 do
    "#{Float.round(num / 1_000, 2)}k"
  end

  defp format_throughput(num) do
    Float.round(num, 2)
  end

  defp start_lsp_server do
    IO.puts(:stderr, "Starting Phronesis LSP server...")
    Phronesis.LSP.Server.run()
  end

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
