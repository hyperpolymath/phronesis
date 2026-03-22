# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Application do
  @moduledoc """
  Application supervisor for Phronesis.

  Starts and supervises:
  - Registry for process naming
  - Consensus cluster (optional, for distributed mode)
  """

  use Application
  require Logger

  @impl true
  def start(_type, _args) do
    # Start Ra application if not already started
    ensure_ra_started()

    children =
      [
        # Registry for naming processes
        {Registry, keys: :unique, name: Phronesis.Registry},

        # Consensus supervisor (optional - only in distributed mode)
        {Phronesis.Consensus.Supervisor, []}
      ] ++ hot_reload_children()

    opts = [strategy: :one_for_one, name: Phronesis.Supervisor]
    Supervisor.start_link(children, opts)
  end

  defp hot_reload_children do
    if Application.get_env(:phronesis, :hot_reload, Mix.env() == :dev) do
      [{Phronesis.HotReload, []}]
    else
      []
    end
  end

  defp ensure_ra_started do
    case Application.ensure_all_started(:ra) do
      {:ok, _} -> :ok
      {:error, _} -> Logger.warn("Failed to start Ra application")
    end
  end
end
