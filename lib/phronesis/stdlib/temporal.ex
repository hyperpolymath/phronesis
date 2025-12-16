# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.StdTemporal do
  @moduledoc """
  Temporal logic operators module.

  Provides bounded temporal operators for policy conditions.
  These replace built-in temporal syntax with bounded, decidable operations.

  ## Functions

  - `eventually(condition, within: duration)` - Condition becomes true within time
  - `always(condition)` - Condition is always true (checked at evaluation time)
  - `since(condition, event)` - Condition has been true since event

  ## Example

      POLICY eventual_convergence:
        Std.Temporal.eventually(routes_stable, within: 30000)
        THEN REPORT("Convergence achieved")
        PRIORITY: 50

  ## Decidability

  All temporal operators are bounded to ensure termination:
  - `eventually` has a required `within` parameter
  - `always` checks current state only (not infinite future)
  - `since` is bounded by event history
  """

  @behaviour Phronesis.Stdlib.Module

  @type duration_ms :: non_neg_integer()
  @type condition :: boolean() | (() -> boolean())

  @impl true
  def call(args) do
    case args do
      [condition | opts] -> eventually(condition, normalize_opts(opts))
      _ -> {:error, :invalid_args}
    end
  end

  @doc """
  Check if a condition becomes true within a duration.

  This is a bounded temporal operator - it will timeout and return false
  if the condition doesn't become true within the specified time.

  ## Options

  - `:within` - Maximum time to wait in milliseconds (required)
  - `:check_interval` - How often to check in ms (default: 100)
  """
  @spec eventually(condition(), keyword()) :: boolean()
  def eventually(condition, opts) do
    within = Keyword.fetch!(opts, :within)
    interval = Keyword.get(opts, :check_interval, 100)

    deadline = System.monotonic_time(:millisecond) + within
    check_until(condition, deadline, interval)
  end

  @doc """
  Check if a condition is currently true.

  Note: This checks the current state only. True "always" over infinite
  time is undecidable, so this is a point-in-time check.
  """
  @spec always(condition()) :: boolean()
  def always(condition) when is_boolean(condition), do: condition
  def always(condition) when is_function(condition, 0), do: condition.()

  @doc """
  Check if a condition has been true since an event occurred.

  Looks up the event in the history and checks condition status.
  """
  @spec since(condition(), any()) :: boolean()
  def since(condition, _event) do
    # In production, this would:
    # 1. Look up when the event occurred
    # 2. Check condition history since then
    # For now, just check current state
    always(condition)
  end

  @doc """
  Create a duration value (helper for cleaner syntax).
  """
  @spec seconds(number()) :: duration_ms()
  def seconds(n), do: round(n * 1000)

  @spec minutes(number()) :: duration_ms()
  def minutes(n), do: round(n * 60_000)

  # Private: check condition until deadline

  defp check_until(condition, deadline, interval) do
    now = System.monotonic_time(:millisecond)

    cond do
      evaluate_condition(condition) -> true
      now >= deadline -> false
      true ->
        Process.sleep(interval)
        check_until(condition, deadline, interval)
    end
  end

  defp evaluate_condition(condition) when is_boolean(condition), do: condition
  defp evaluate_condition(condition) when is_function(condition, 0), do: condition.()

  defp normalize_opts(opts) when is_list(opts) do
    Enum.map(opts, fn
      {key, value} when is_binary(key) -> {String.to_atom(key), value}
      {key, value} -> {key, value}
    end)
  end
end
