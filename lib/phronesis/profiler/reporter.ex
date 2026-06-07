# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Profiler.Reporter do
  @moduledoc """
  Advanced reporting and visualization for profiling data.

  Generates detailed reports, charts, and comparisons for performance analysis.
  """

  alias Phronesis.Profiler

  @doc """
  Generate a detailed HTML report.
  """
  def html_report(session, output_file) do
    html = """
    <!DOCTYPE html>
    <html>
    <head>
      <title>Phronesis Profile Report - #{Path.basename(session.file)}</title>
      <style>
        body { font-family: monospace; margin: 40px; background: #1e1e1e; color: #d4d4d4; }
        h1, h2, h3 { color: #4ec9b0; }
        .stat { margin: 10px 0; }
        .hotspot { background: #2d2d30; padding: 10px; margin: 10px 0; border-left: 3px solid #f48771; }
        .policy { background: #2d2d30; padding: 10px; margin: 10px 0; }
        .metric { display: inline-block; margin-right: 20px; }
        .metric-label { color: #9cdcfe; }
        .metric-value { color: #ce9178; font-weight: bold; }
        table { border-collapse: collapse; width: 100%; margin: 20px 0; }
        th, td { border: 1px solid #3e3e42; padding: 8px; text-align: left; }
        th { background: #2d2d30; color: #4ec9b0; }
        .bar { background: #569cd6; height: 20px; }
        .summary { background: #2d2d30; padding: 20px; margin: 20px 0; }
      </style>
    </head>
    <body>
      <h1>Phronesis Profile Report</h1>
      <div class="summary">
        #{html_summary(session)}
      </div>

      <h2>Policy Statistics</h2>
      #{html_policy_stats(session)}

      <h2>Top Hotspots</h2>
      #{html_hotspots(session.hotspots)}

      <h2>Memory Usage</h2>
      #{html_memory(session.memory_stats)}
    </body>
    </html>
    """

    File.write(output_file, html)
  end

  @doc """
  Generate a CSV report for spreadsheet analysis.
  """
  def csv_report(session, output_file) do
    total_time = session.end_time - session.start_time

    csv =
      "Policy,Executions,Total Time (μs),Avg Time (μs),Min Time (μs),Max Time (μs),% of Total\n" <>
        Enum.map_join(session.policy_stats, "\n", fn {name, stats} ->
          percentage = stats.total_time / total_time * 100

          "#{name},#{stats.count},#{stats.total_time},#{round(stats.avg_time)}," <>
            "#{stats.min_time},#{stats.max_time},#{Float.round(percentage, 2)}"
        end)

    File.write(output_file, csv)
  end

  @doc """
  Generate a markdown report.
  """
  def markdown_report(session) do
    total_time = session.end_time - session.start_time

    """
    # Phronesis Profile Report

    **File:** `#{session.file}`
    **Total Time:** #{Profiler.format_report(session) |> extract_total_time()}

    ## Summary

    - **Policies Profiled:** #{map_size(session.policy_stats)}
    - **Total Execution Time:** #{format_time(total_time)}
    - **Memory Delta:** #{format_bytes(session.memory_stats.delta)}

    ## Policy Performance

    | Policy | Executions | Total Time | Avg Time | % of Total |
    |--------|-----------|------------|----------|------------|
    #{markdown_policy_table(session, total_time)}

    ## Top Hotspots

    #{markdown_hotspots(session.hotspots)}

    ## Memory Usage

    - **Start:** #{format_bytes(session.memory_stats.start)}
    - **End:** #{format_bytes(session.memory_stats.end)}
    - **Delta:** #{format_bytes(session.memory_stats.delta)}
    """
  end

  @doc """
  Interactive profiler CLI.
  """
  def interactive(session) do
    IO.puts("Phronesis Profiler - Interactive Mode")
    IO.puts("Type 'help' for commands, 'quit' to exit\n")

    print_summary(session)
    interactive_loop(session)
  end

  ## HTML Helpers

  defp html_summary(session) do
    total_time = session.end_time - session.start_time

    """
    <div class="metric">
      <span class="metric-label">File:</span>
      <span class="metric-value">#{session.file}</span>
    </div>
    <div class="metric">
      <span class="metric-label">Total Time:</span>
      <span class="metric-value">#{format_time(total_time)}</span>
    </div>
    <div class="metric">
      <span class="metric-label">Policies:</span>
      <span class="metric-value">#{map_size(session.policy_stats)}</span>
    </div>
    <div class="metric">
      <span class="metric-label">Memory Delta:</span>
      <span class="metric-value">#{format_bytes(session.memory_stats.delta)}</span>
    </div>
    """
  end

  defp html_policy_stats(session) do
    total_time = session.end_time - session.start_time

    """
    <table>
      <tr>
        <th>Policy</th>
        <th>Executions</th>
        <th>Total Time</th>
        <th>Avg Time</th>
        <th>% of Total</th>
        <th>Visual</th>
      </tr>
      #{Enum.map_join(session.policy_stats, "\n", fn {name, stats} ->
        percentage = stats.total_time / total_time * 100

        """
        <tr>
          <td>#{name}</td>
          <td>#{stats.count}</td>
          <td>#{format_time(stats.total_time)}</td>
          <td>#{format_time(round(stats.avg_time))}</td>
          <td>#{Float.round(percentage, 2)}%</td>
          <td><div class="bar" style="width: #{min(percentage * 5, 100)}%"></div></td>
        </tr>
        """
      end)}
    </table>
    """
  end

  defp html_hotspots(hotspots) do
    hotspots
    |> Enum.take(5)
    |> Enum.with_index(1)
    |> Enum.map_join("\n", fn {hotspot, idx} ->
      """
      <div class="hotspot">
        <strong>#{idx}. #{hotspot.name}</strong> (#{hotspot.type})<br>
        Time: #{Float.round(hotspot.time_ms, 3)} ms (#{Float.round(hotspot.percentage, 2)}%)<br>
        Calls: #{hotspot.count}<br>
        Avg: #{Float.round(hotspot.avg_time / 1000, 3)} ms
      </div>
      """
    end)
  end

  defp html_memory(memory_stats) do
    """
    <div class="policy">
      <div class="metric">
        <span class="metric-label">Start:</span>
        <span class="metric-value">#{format_bytes(memory_stats.start)}</span>
      </div>
      <div class="metric">
        <span class="metric-label">End:</span>
        <span class="metric-value">#{format_bytes(memory_stats.end)}</span>
      </div>
      <div class="metric">
        <span class="metric-label">Delta:</span>
        <span class="metric-value">#{format_bytes(memory_stats.delta)}</span>
      </div>
    </div>
    """
  end

  ## Markdown Helpers

  defp markdown_policy_table(session, total_time) do
    session.policy_stats
    |> Enum.map_join("\n", fn {name, stats} ->
      percentage = stats.total_time / total_time * 100

      "| #{name} | #{stats.count} | #{format_time(stats.total_time)} | " <>
        "#{format_time(round(stats.avg_time))} | #{Float.round(percentage, 2)}% |"
    end)
  end

  defp markdown_hotspots(hotspots) do
    hotspots
    |> Enum.take(5)
    |> Enum.with_index(1)
    |> Enum.map_join("\n\n", fn {hotspot, idx} ->
      """
      ### #{idx}. #{hotspot.name}

      - **Type:** #{hotspot.type}
      - **Time:** #{Float.round(hotspot.time_ms, 3)} ms (#{Float.round(hotspot.percentage, 2)}%)
      - **Calls:** #{hotspot.count}
      - **Average:** #{Float.round(hotspot.avg_time / 1000, 3)} ms
      """
    end)
  end

  ## Interactive CLI

  defp interactive_loop(session) do
    case IO.gets("(profile) ") do
      :eof ->
        IO.puts("\nExiting profiler")
        :ok

      {:error, reason} ->
        IO.puts(:stderr, "Error: #{inspect(reason)}")
        interactive_loop(session)

      input ->
        command = String.trim(input)
        handle_command(command, session)
    end
  end

  defp handle_command("help", session) do
    IO.puts("""
    Profiler Commands:
      summary          Show profiling summary
      policies         List all policy statistics
      hotspots         Show top performance hotspots
      memory           Show memory usage
      policy <name>    Show stats for specific policy
      export html      Export HTML report
      export csv       Export CSV report
      export md        Export markdown report
      help             Show this help
      quit             Exit profiler
    """)

    interactive_loop(session)
  end

  defp handle_command("summary", session) do
    print_summary(session)
    interactive_loop(session)
  end

  defp handle_command("policies", session) do
    print_policies(session)
    interactive_loop(session)
  end

  defp handle_command("hotspots", session) do
    print_hotspots(session.hotspots)
    interactive_loop(session)
  end

  defp handle_command("memory", session) do
    print_memory(session.memory_stats)
    interactive_loop(session)
  end

  defp handle_command("policy " <> name, session) do
    print_policy(session, String.trim(name))
    interactive_loop(session)
  end

  defp handle_command("export html", session) do
    filename = "profile_#{:os.system_time(:second)}.html"
    html_report(session, filename)
    IO.puts("Exported HTML report to: #{filename}")
    interactive_loop(session)
  end

  defp handle_command("export csv", session) do
    filename = "profile_#{:os.system_time(:second)}.csv"
    csv_report(session, filename)
    IO.puts("Exported CSV report to: #{filename}")
    interactive_loop(session)
  end

  defp handle_command("export md", session) do
    filename = "profile_#{:os.system_time(:second)}.md"
    File.write(filename, markdown_report(session))
    IO.puts("Exported Markdown report to: #{filename}")
    interactive_loop(session)
  end

  defp handle_command("quit", _session) do
    IO.puts("Exiting profiler")
    :ok
  end

  defp handle_command("", session) do
    interactive_loop(session)
  end

  defp handle_command(cmd, session) do
    IO.puts("Unknown command: #{cmd}")
    IO.puts("Type 'help' for available commands")
    interactive_loop(session)
  end

  defp print_summary(session) do
    total_time = session.end_time - session.start_time

    IO.puts("""
    === Profile Summary ===
    File: #{session.file}
    Total Time: #{format_time(total_time)}
    Policies: #{map_size(session.policy_stats)}
    Memory Delta: #{format_bytes(session.memory_stats.delta)}
    """)
  end

  defp print_policies(session) do
    total_time = session.end_time - session.start_time

    IO.puts("=== Policy Statistics ===\n")

    session.policy_stats
    |> Enum.each(fn {name, stats} ->
      percentage = stats.total_time / total_time * 100

      IO.puts("""
      #{name}:
        Executions: #{stats.count}
        Total: #{format_time(stats.total_time)}
        Avg: #{format_time(round(stats.avg_time))}
        Min: #{format_time(stats.min_time)}
        Max: #{format_time(stats.max_time)}
        % of total: #{Float.round(percentage, 2)}%
      """)
    end)
  end

  defp print_hotspots(hotspots) do
    IO.puts("=== Top Hotspots ===\n")

    hotspots
    |> Enum.take(5)
    |> Enum.with_index(1)
    |> Enum.each(fn {hotspot, idx} ->
      IO.puts("""
      #{idx}. #{hotspot.name} (#{hotspot.type})
         Time: #{Float.round(hotspot.time_ms, 3)} ms (#{Float.round(hotspot.percentage, 2)}%)
         Calls: #{hotspot.count}
         Avg: #{Float.round(hotspot.avg_time / 1000, 3)} ms
      """)
    end)
  end

  defp print_memory(memory_stats) do
    IO.puts("""
    === Memory Usage ===
    Start: #{format_bytes(memory_stats.start)}
    End: #{format_bytes(memory_stats.end)}
    Delta: #{format_bytes(memory_stats.delta)}
    """)
  end

  defp print_policy(session, name) do
    case Map.fetch(session.policy_stats, name) do
      {:ok, stats} ->
        total_time = session.end_time - session.start_time
        percentage = stats.total_time / total_time * 100

        IO.puts("""
        === Policy: #{name} ===
        Executions: #{stats.count}
        Total Time: #{format_time(stats.total_time)}
        Avg Time: #{format_time(round(stats.avg_time))}
        Min Time: #{format_time(stats.min_time)}
        Max Time: #{format_time(stats.max_time)}
        % of Total: #{Float.round(percentage, 2)}%
        """)

      :error ->
        IO.puts("Policy '#{name}' not found in profile data")
    end
  end

  ## Helpers

  defp extract_total_time(report) do
    case Regex.run(~r/Total Time: (.+)/, report) do
      [_, time] -> time
      _ -> "N/A"
    end
  end

  defp format_time(microseconds) when is_integer(microseconds) do
    cond do
      microseconds < 1_000 ->
        "#{microseconds} μs"

      microseconds < 1_000_000 ->
        "#{Float.round(microseconds / 1_000, 2)} ms"

      true ->
        "#{Float.round(microseconds / 1_000_000, 2)} s"
    end
  end

  defp format_time(_), do: "N/A"

  defp format_bytes(bytes) when is_integer(bytes) do
    cond do
      bytes < 1024 ->
        "#{bytes} B"

      bytes < 1024 * 1024 ->
        "#{Float.round(bytes / 1024, 2)} KB"

      bytes < 1024 * 1024 * 1024 ->
        "#{Float.round(bytes / (1024 * 1024), 2)} MB"

      true ->
        "#{Float.round(bytes / (1024 * 1024 * 1024), 2)} GB"
    end
  end

  defp format_bytes(_), do: "N/A"
end
