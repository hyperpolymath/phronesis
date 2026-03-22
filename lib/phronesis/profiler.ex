# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Profiler do
  @moduledoc """
  Performance profiler for Phronesis policies.

  Tracks execution time, call counts, and resource usage for policies,
  functions, and consensus operations.

  ## Features

  - Measure policy execution time
  - Track function call counts and timing
  - Profile consensus operations
  - Identify hotspots and bottlenecks
  - Generate performance reports
  - Compare runs and track regressions
  - Memory usage tracking

  ## Usage

      # Start profiling
      {:ok, session} = Profiler.start("policy.phr")

      # Run with profiling
      {:ok, report} = Profiler.run(session)

      # Generate report
      Profiler.format_report(report)

      # Profile specific policy
      Profiler.profile_policy(policy_name)
  """

  alias Phronesis.{Lexer, Parser, TracingInterpreter, State, Trace}

  defstruct [
    :file,
    :ast,
    :state,
    :start_time,
    :end_time,
    :policy_stats,
    :function_stats,
    :consensus_stats,
    :memory_stats,
    :call_graph,
    :hotspots
  ]

  @type timing :: %{
          count: integer(),
          total_time: integer(),
          min_time: integer(),
          max_time: integer(),
          avg_time: float()
        }

  @type policy_stat :: %{
          name: String.t(),
          executions: integer(),
          total_time: integer(),
          avg_time: float(),
          percentage: float()
        }

  @type t :: %__MODULE__{
          file: String.t(),
          ast: [term()],
          state: State.t(),
          start_time: integer(),
          end_time: integer() | nil,
          policy_stats: %{String.t() => timing()},
          function_stats: %{String.t() => timing()},
          consensus_stats: %{String.t() => timing()},
          memory_stats: %{atom() => integer()},
          call_graph: %{String.t() => [String.t()]},
          hotspots: [term()]
        }

  ## Session Management

  @doc """
  Start a profiling session for a policy file.
  """
  def start(file_path) do
    with {:ok, source} <- File.read(file_path),
         {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      session = %__MODULE__{
        file: file_path,
        ast: ast,
        state: State.new(),
        start_time: System.monotonic_time(:microsecond),
        end_time: nil,
        policy_stats: %{},
        function_stats: %{},
        consensus_stats: %{},
        memory_stats: initial_memory_stats(),
        call_graph: %{},
        hotspots: []
      }

      {:ok, session}
    else
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Load context for profiling.
  """
  def load_context(session, context) do
    state = Map.merge(session.state, context)
    %{session | state: state}
  end

  ## Profiling Execution

  @doc """
  Run the policy with profiling enabled.
  """
  def run(session) do
    start_time = System.monotonic_time(:microsecond)
    start_memory = get_memory_usage()

    result =
      case profile_execution(session.ast, session.state) do
        {:ok, final_state, stats} ->
          end_time = System.monotonic_time(:microsecond)
          end_memory = get_memory_usage()

          session = %{
            session
            | state: final_state,
              start_time: start_time,
              end_time: end_time,
              policy_stats: stats.policies,
              function_stats: stats.functions,
              consensus_stats: stats.consensus,
              memory_stats: %{
                start: start_memory,
                end: end_memory,
                delta: end_memory - start_memory
              }
          }

          session = analyze_hotspots(session)
          {:ok, session}

        {:error, reason} ->
          {:error, reason}
      end

    result
  end

  @doc """
  Profile a specific policy by name.
  """
  def profile_policy(session, policy_name) do
    policy = Enum.find(session.ast, fn
      {:policy, ^policy_name, _, _, _} -> true
      _ -> false
    end)

    case policy do
      nil ->
        {:error, :policy_not_found}

      policy_ast ->
        start_time = System.monotonic_time(:microsecond)

        result =
          case TracingInterpreter.execute([policy_ast], session.state) do
            {:ok, final_state, _trace} ->
              end_time = System.monotonic_time(:microsecond)
              elapsed = end_time - start_time

              {:ok, %{
                policy: policy_name,
                time: elapsed,
                time_ms: elapsed / 1000.0,
                state: final_state
              }}

            {:error, reason} ->
              {:error, reason}
          end

        result
    end
  end

  @doc """
  Run multiple iterations for statistical profiling.
  """
  def benchmark(session, iterations \\ 100) do
    times =
      Enum.map(1..iterations, fn _i ->
        start = System.monotonic_time(:microsecond)

        case TracingInterpreter.execute(session.ast, session.state) do
          {:ok, _, _} ->
            System.monotonic_time(:microsecond) - start

          {:error, _} ->
            nil
        end
      end)
      |> Enum.reject(&is_nil/1)

    if Enum.empty?(times) do
      {:error, :all_iterations_failed}
    else
      stats = calculate_statistics(times)
      {:ok, stats}
    end
  end

  ## Internal Profiling

  defp profile_execution(ast, state) do
    stats = %{
      policies: %{},
      functions: %{},
      consensus: %{}
    }

    profile_nodes(ast, state, stats)
  end

  defp profile_nodes([], state, stats) do
    {:ok, state, stats}
  end

  defp profile_nodes([node | rest], state, stats) do
    {new_state, new_stats} = profile_node(node, state, stats)
    profile_nodes(rest, new_state, new_stats)
  end

  defp profile_node({:policy, name, _cond, _action, _meta} = policy, state, stats) do
    start_time = System.monotonic_time(:microsecond)

    {new_state, _trace} =
      case TracingInterpreter.execute([policy], state) do
        {:ok, s, t} -> {s, t}
        {:error, _} -> {state, Trace.new()}
      end

    end_time = System.monotonic_time(:microsecond)
    elapsed = end_time - start_time

    new_stats = update_timing_stats(stats.policies, name, elapsed)
    stats = %{stats | policies: new_stats}

    {new_state, stats}
  end

  defp profile_node({:const, _name, _value, _meta}, state, stats) do
    # Constants don't need profiling
    {state, stats}
  end

  defp profile_node({:import, _module, _meta}, state, stats) do
    # Imports don't need profiling
    {state, stats}
  end

  defp profile_node(_, state, stats) do
    {state, stats}
  end

  defp update_timing_stats(stats_map, name, elapsed_time) do
    current = Map.get(stats_map, name, %{
      count: 0,
      total_time: 0,
      min_time: :infinity,
      max_time: 0
    })

    new_count = current.count + 1
    new_total = current.total_time + elapsed_time
    new_min = min(current.min_time, elapsed_time)
    new_max = max(current.max_time, elapsed_time)
    new_avg = new_total / new_count

    updated = %{
      count: new_count,
      total_time: new_total,
      min_time: new_min,
      max_time: new_max,
      avg_time: new_avg
    }

    Map.put(stats_map, name, updated)
  end

  ## Analysis

  defp analyze_hotspots(session) do
    total_time = session.end_time - session.start_time

    hotspots =
      session.policy_stats
      |> Enum.map(fn {name, stats} ->
        percentage = stats.total_time / total_time * 100

        %{
          type: :policy,
          name: name,
          time: stats.total_time,
          time_ms: stats.total_time / 1000.0,
          percentage: percentage,
          count: stats.count,
          avg_time: stats.avg_time
        }
      end)
      |> Enum.sort_by(& &1.percentage, :desc)

    %{session | hotspots: hotspots}
  end

  defp calculate_statistics(times) do
    count = length(times)
    total = Enum.sum(times)
    avg = total / count
    sorted = Enum.sort(times)
    min_time = List.first(sorted)
    max_time = List.last(sorted)

    median =
      if rem(count, 2) == 0 do
        (Enum.at(sorted, div(count, 2) - 1) + Enum.at(sorted, div(count, 2))) / 2
      else
        Enum.at(sorted, div(count, 2))
      end

    p95_idx = round(count * 0.95) - 1
    p99_idx = round(count * 0.99) - 1

    %{
      count: count,
      total: total,
      avg: avg,
      median: median,
      min: min_time,
      max: max_time,
      p95: Enum.at(sorted, p95_idx),
      p99: Enum.at(sorted, p99_idx),
      times: times
    }
  end

  ## Memory Tracking

  defp initial_memory_stats do
    %{
      start: get_memory_usage(),
      end: 0,
      delta: 0
    }
  end

  defp get_memory_usage do
    :erlang.memory(:total)
  end

  ## Reporting

  @doc """
  Format profiling report for display.
  """
  def format_report(session) do
    total_time = session.end_time - session.start_time
    total_time_ms = total_time / 1000.0

    """
    === Phronesis Profiler Report ===
    File: #{session.file}
    Total Time: #{format_time(total_time)} (#{Float.round(total_time_ms, 2)} ms)
    Memory Delta: #{format_bytes(session.memory_stats.delta)}

    #{format_policy_stats(session, total_time)}

    #{format_hotspots(session.hotspots)}

    #{format_memory_stats(session.memory_stats)}
    """
  end

  @doc """
  Generate JSON report for automated analysis.
  """
  def json_report(session) do
    %{
      file: session.file,
      total_time: session.end_time - session.start_time,
      policies: format_policy_stats_json(session.policy_stats),
      functions: format_function_stats_json(session.function_stats),
      consensus: format_consensus_stats_json(session.consensus_stats),
      memory: session.memory_stats,
      hotspots: session.hotspots
    }
  end

  defp format_policy_stats(session, total_time) do
    if map_size(session.policy_stats) == 0 do
      "No policies profiled"
    else
      header = "Policy Statistics:\n"

      rows =
        session.policy_stats
        |> Enum.map(fn {name, stats} ->
          percentage = stats.total_time / total_time * 100
          "  #{name}\n" <>
            "    Executions: #{stats.count}\n" <>
            "    Total: #{format_time(stats.total_time)}\n" <>
            "    Avg: #{format_time(round(stats.avg_time))}\n" <>
            "    Min: #{format_time(stats.min_time)}\n" <>
            "    Max: #{format_time(stats.max_time)}\n" <>
            "    % of total: #{Float.round(percentage, 2)}%"
        end)
        |> Enum.join("\n\n")

      header <> rows
    end
  end

  defp format_hotspots(hotspots) do
    if Enum.empty?(hotspots) do
      "No hotspots identified"
    else
      header = "Top Hotspots:\n"

      rows =
        hotspots
        |> Enum.take(5)
        |> Enum.with_index(1)
        |> Enum.map(fn {hotspot, idx} ->
          "  #{idx}. #{hotspot.name} (#{hotspot.type})\n" <>
            "     Time: #{Float.round(hotspot.time_ms, 3)} ms (#{Float.round(hotspot.percentage, 2)}%)\n" <>
            "     Calls: #{hotspot.count}\n" <>
            "     Avg: #{Float.round(hotspot.avg_time / 1000, 3)} ms"
        end)
        |> Enum.join("\n\n")

      header <> rows
    end
  end

  defp format_memory_stats(memory_stats) do
    """
    Memory Usage:
      Start: #{format_bytes(memory_stats.start)}
      End: #{format_bytes(memory_stats.end)}
      Delta: #{format_bytes(memory_stats.delta)}
    """
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

  defp format_policy_stats_json(stats) do
    Enum.into(stats, %{})
  end

  defp format_function_stats_json(stats) do
    Enum.into(stats, %{})
  end

  defp format_consensus_stats_json(stats) do
    Enum.into(stats, %{})
  end

  ## Comparison

  @doc """
  Compare two profiling sessions to detect regressions.
  """
  def compare(baseline, current) do
    policy_changes =
      compare_stats(baseline.policy_stats, current.policy_stats)

    total_time_baseline = baseline.end_time - baseline.start_time
    total_time_current = current.end_time - current.start_time
    time_delta = total_time_current - total_time_baseline
    time_percent = time_delta / total_time_baseline * 100

    %{
      total_time_change: %{
        baseline: total_time_baseline,
        current: total_time_current,
        delta: time_delta,
        percent: time_percent
      },
      policy_changes: policy_changes,
      regressions: find_regressions(policy_changes),
      improvements: find_improvements(policy_changes)
    }
  end

  defp compare_stats(baseline, current) do
    all_keys = MapSet.union(MapSet.new(Map.keys(baseline)), MapSet.new(Map.keys(current)))

    Enum.map(all_keys, fn key ->
      baseline_stat = Map.get(baseline, key)
      current_stat = Map.get(current, key)

      cond do
        is_nil(baseline_stat) ->
          {key, :new, current_stat}

        is_nil(current_stat) ->
          {key, :removed, baseline_stat}

        true ->
          delta = current_stat.avg_time - baseline_stat.avg_time
          percent = delta / baseline_stat.avg_time * 100

          {key, :changed, %{
            baseline: baseline_stat,
            current: current_stat,
            delta: delta,
            percent: percent
          }}
      end
    end)
  end

  defp find_regressions(changes) do
    Enum.filter(changes, fn
      {_name, :changed, %{percent: p}} when p > 10.0 -> true
      _ -> false
    end)
  end

  defp find_improvements(changes) do
    Enum.filter(changes, fn
      {_name, :changed, %{percent: p}} when p < -10.0 -> true
      _ -> false
    end)
  end
end
