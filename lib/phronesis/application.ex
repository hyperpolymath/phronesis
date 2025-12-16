# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      # Registry for module lookups
      {Registry, keys: :unique, name: Phronesis.ModuleRegistry}
    ]

    opts = [strategy: :one_for_one, name: Phronesis.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
