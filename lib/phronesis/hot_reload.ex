# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.HotReload do
  @moduledoc """
  Hot code reloading for Phronesis development.

  Automatically recompiles and reloads changed modules without
  restarting the application.

  ## Usage

      # Start watching for changes
      Phronesis.HotReload.start()

      # Stop watching
      Phronesis.HotReload.stop()

      # Manually reload a module
      Phronesis.HotReload.reload_module(Phronesis.Parser)

      # Reload all Phronesis modules
      Phronesis.HotReload.reload_all()

  ## Development Mode

  Hot reloading is automatically enabled in development mode.
  Set `config :phronesis, hot_reload: false` to disable.
  """

  use GenServer
  require Logger

  @watch_interval 1000  # Check for changes every second
  @phronesis_modules_pattern "lib/phronesis/**/*.ex"

  # ============================================================
  # Public API
  # ============================================================

  @doc """
  Start the hot reload server.
  """
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc """
  Start watching for file changes.
  """
  def start do
    if enabled?() do
      case GenServer.whereis(__MODULE__) do
        nil ->
          start_link()

        pid when is_pid(pid) ->
          {:ok, pid}
      end
    else
      {:error, :disabled}
    end
  end

  @doc """
  Stop watching for file changes.
  """
  def stop do
    case GenServer.whereis(__MODULE__) do
      nil -> :ok
      pid -> GenServer.stop(pid)
    end
  end

  @doc """
  Manually reload a specific module.
  """
  def reload_module(module) when is_atom(module) do
    case Code.ensure_loaded(module) do
      {:module, ^module} ->
        case :code.purge(module) do
          true ->
            case :code.load_file(module) do
              {:module, ^module} ->
                Logger.info("Hot reloaded: #{inspect(module)}")
                {:ok, module}

              {:error, reason} ->
                {:error, {:load_failed, reason}}
            end

          false ->
            {:error, :purge_failed}
        end

      {:error, reason} ->
        {:error, {:not_loaded, reason}}
    end
  end

  @doc """
  Reload all Phronesis modules.
  """
  def reload_all do
    modules = get_phronesis_modules()

    results =
      Enum.map(modules, fn module ->
        case reload_module(module) do
          {:ok, _} -> {:ok, module}
          {:error, reason} -> {:error, module, reason}
        end
      end)

    success_count = Enum.count(results, &match?({:ok, _}, &1))
    failure_count = Enum.count(results, &match?({:error, _, _}, &1))

    Logger.info("Hot reload complete: #{success_count} success, #{failure_count} failures")

    {:ok, results}
  end

  @doc """
  Recompile changed files and reload modules.
  """
  def recompile do
    Logger.info("Recompiling changed files...")

    case IEx.Helpers.recompile() do
      {:ok, modules} ->
        Logger.info("Recompiled #{length(modules)} modules")
        {:ok, modules}

      {:error, modules, warnings} ->
        Logger.warn("Recompile completed with warnings: #{inspect(warnings)}")
        {:ok, modules}
    end
  end

  # ============================================================
  # GenServer Callbacks
  # ============================================================

  @impl true
  def init(_opts) do
    if enabled?() do
      Logger.info("Hot reload enabled - watching for changes")

      # Get initial file timestamps
      files = get_watched_files()
      timestamps = get_file_timestamps(files)

      # Schedule first check
      schedule_check()

      {:ok, %{timestamps: timestamps}}
    else
      {:stop, :disabled}
    end
  end

  @impl true
  def handle_info(:check_changes, state) do
    # Check for file changes
    files = get_watched_files()
    new_timestamps = get_file_timestamps(files)

    changed_files =
      Enum.filter(files, fn file ->
        old_mtime = Map.get(state.timestamps, file)
        new_mtime = Map.get(new_timestamps, file)

        old_mtime != nil and new_mtime != nil and new_mtime > old_mtime
      end)

    # Reload if files changed
    if changed_files != [] do
      Logger.info("Detected changes in #{length(changed_files)} files")

      Enum.each(changed_files, fn file ->
        Logger.debug("  Changed: #{file}")
      end)

      # Recompile and reload
      case recompile() do
        {:ok, modules} ->
          Logger.info("Hot reload successful")
          {:ok, modules}

        {:error, reason} ->
          Logger.error("Hot reload failed: #{inspect(reason)}")
          {:error, reason}
      end
    end

    # Schedule next check
    schedule_check()

    {:noreply, %{state | timestamps: new_timestamps}}
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  defp enabled? do
    Application.get_env(:phronesis, :hot_reload, Mix.env() == :dev)
  end

  defp schedule_check do
    Process.send_after(self(), :check_changes, @watch_interval)
  end

  defp get_watched_files do
    Path.wildcard(@phronesis_modules_pattern)
  end

  defp get_file_timestamps(files) do
    Map.new(files, fn file ->
      case File.stat(file) do
        {:ok, %{mtime: mtime}} -> {file, mtime}
        {:error, _} -> {file, nil}
      end
    end)
  end

  defp get_phronesis_modules do
    :code.all_loaded()
    |> Enum.filter(fn {module, _} ->
      module
      |> Atom.to_string()
      |> String.starts_with?("Elixir.Phronesis")
    end)
    |> Enum.map(fn {module, _} -> module end)
  end
end
