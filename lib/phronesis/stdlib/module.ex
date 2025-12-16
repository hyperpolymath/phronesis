# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.Module do
  @moduledoc """
  Behaviour for Phronesis standard library modules.

  All Std.* modules must implement this behaviour to be callable
  from Phronesis policy code.

  ## Example Implementation

      defmodule Phronesis.Stdlib.StdMyModule do
        @behaviour Phronesis.Stdlib.Module

        @impl true
        def call(args) do
          case args do
            [x, y] -> do_something(x, y)
            _ -> {:error, :invalid_args}
          end
        end
      end
  """

  @doc """
  Called when the module function is invoked from Phronesis code.

  Receives a list of evaluated arguments.
  Returns the result value.
  """
  @callback call(args :: [any()]) :: any()
end
