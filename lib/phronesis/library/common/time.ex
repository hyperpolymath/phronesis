# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Library.Common.Time do
  @moduledoc """
  Common time utilities for network policy languages.

  Provides time-based operations for policy scheduling, expiration,
  and temporal constraints.
  """

  # ============================================================
  # Time Parsing
  # ============================================================

  @doc """
  Parse a duration string into milliseconds.

  Supported formats:
  - "30s" -> 30 seconds
  - "5m" -> 5 minutes
  - "2h" -> 2 hours
  - "1d" -> 1 day
  - "1w" -> 1 week
  """
  @spec parse_duration(String.t()) :: {:ok, non_neg_integer()} | {:error, :invalid_duration}
  def parse_duration(str) when is_binary(str) do
    case Regex.run(~r/^(\d+)(ms|s|m|h|d|w)$/, str) do
      [_, value, unit] ->
        {n, ""} = Integer.parse(value)
        {:ok, n * unit_to_ms(unit)}

      nil ->
        {:error, :invalid_duration}
    end
  end

  @doc """
  Parse a time window specification.

  Examples:
  - "08:00-17:00" -> business hours
  - "00:00-06:00" -> night window
  """
  @spec parse_time_window(String.t()) :: {:ok, {Time.t(), Time.t()}} | {:error, term()}
  def parse_time_window(str) when is_binary(str) do
    case String.split(str, "-") do
      [start_str, end_str] ->
        with {:ok, start_time} <- Time.from_iso8601(start_str <> ":00"),
             {:ok, end_time} <- Time.from_iso8601(end_str <> ":00") do
          {:ok, {start_time, end_time}}
        end

      _ ->
        {:error, :invalid_time_window}
    end
  end

  @doc """
  Parse a schedule specification.

  Examples:
  - "weekdays 08:00-17:00"
  - "weekend 00:00-23:59"
  - "monday,wednesday,friday 09:00-18:00"
  """
  @spec parse_schedule(String.t()) :: {:ok, map()} | {:error, term()}
  def parse_schedule(str) when is_binary(str) do
    case String.split(str, " ", parts: 2) do
      [days_str, window_str] ->
        with {:ok, days} <- parse_days(days_str),
             {:ok, window} <- parse_time_window(window_str) do
          {:ok, %{days: days, window: window}}
        end

      _ ->
        {:error, :invalid_schedule}
    end
  end

  # ============================================================
  # Time Checks
  # ============================================================

  @doc """
  Check if a datetime is within a time window.
  """
  @spec in_time_window?(DateTime.t() | Time.t(), {Time.t(), Time.t()}) :: boolean()
  def in_time_window?(%DateTime{} = dt, window) do
    time = DateTime.to_time(dt)
    in_time_window?(time, window)
  end

  def in_time_window?(%Time{} = time, {start_time, end_time}) do
    cond do
      # Normal window (e.g., 08:00-17:00)
      Time.compare(start_time, end_time) == :lt ->
        Time.compare(time, start_time) != :lt and
        Time.compare(time, end_time) != :gt

      # Overnight window (e.g., 22:00-06:00)
      Time.compare(start_time, end_time) == :gt ->
        Time.compare(time, start_time) != :lt or
        Time.compare(time, end_time) != :gt

      # Start equals end (24-hour window)
      true ->
        true
    end
  end

  @doc """
  Check if a datetime matches a schedule.
  """
  @spec matches_schedule?(DateTime.t(), map()) :: boolean()
  def matches_schedule?(dt, %{days: days, window: window}) do
    day_of_week = Date.day_of_week(DateTime.to_date(dt))

    day_matches = case days do
      :all -> true
      :weekdays -> day_of_week in 1..5
      :weekend -> day_of_week in [6, 7]
      day_list when is_list(day_list) -> day_of_week in day_list
    end

    day_matches and in_time_window?(dt, window)
  end

  @doc """
  Check if a policy has expired.
  """
  @spec expired?(DateTime.t() | :never, DateTime.t()) :: boolean()
  def expired?(:never, _now), do: false

  def expired?(expires_at, now) do
    DateTime.compare(expires_at, now) == :lt
  end

  @doc """
  Check if a datetime is within a grace period after expiration.
  """
  @spec in_grace_period?(DateTime.t(), DateTime.t(), non_neg_integer()) :: boolean()
  def in_grace_period?(expires_at, now, grace_ms) do
    case DateTime.diff(now, expires_at, :millisecond) do
      diff when diff > 0 and diff <= grace_ms -> true
      _ -> false
    end
  end

  # ============================================================
  # Time Calculations
  # ============================================================

  @doc """
  Add a duration to a datetime.
  """
  @spec add_duration(DateTime.t(), non_neg_integer()) :: DateTime.t()
  def add_duration(dt, ms) do
    DateTime.add(dt, ms, :millisecond)
  end

  @doc """
  Calculate the time until next schedule match.
  """
  @spec time_until_schedule(DateTime.t(), map()) :: non_neg_integer() | :never
  def time_until_schedule(dt, schedule) do
    if matches_schedule?(dt, schedule) do
      0
    else
      find_next_match(dt, schedule, 0)
    end
  end

  @doc """
  Get the next occurrence of a time window.
  """
  @spec next_window_start(DateTime.t(), {Time.t(), Time.t()}) :: DateTime.t()
  def next_window_start(dt, {start_time, _end_time}) do
    current_time = DateTime.to_time(dt)

    if Time.compare(current_time, start_time) == :lt do
      # Today
      dt
      |> DateTime.to_date()
      |> DateTime.new!(start_time)
    else
      # Tomorrow
      dt
      |> DateTime.to_date()
      |> Date.add(1)
      |> DateTime.new!(start_time)
    end
  end

  # ============================================================
  # Formatting
  # ============================================================

  @doc """
  Format a duration in milliseconds to human-readable string.
  """
  @spec format_duration(non_neg_integer()) :: String.t()
  def format_duration(ms) when ms < 1000, do: "#{ms}ms"
  def format_duration(ms) when ms < 60_000, do: "#{div(ms, 1000)}s"
  def format_duration(ms) when ms < 3_600_000, do: "#{div(ms, 60_000)}m"
  def format_duration(ms) when ms < 86_400_000, do: "#{div(ms, 3_600_000)}h"
  def format_duration(ms), do: "#{div(ms, 86_400_000)}d"

  @doc """
  Format a time window.
  """
  @spec format_time_window({Time.t(), Time.t()}) :: String.t()
  def format_time_window({start_time, end_time}) do
    "#{Time.to_string(start_time) |> String.slice(0..4)}-#{Time.to_string(end_time) |> String.slice(0..4)}"
  end

  # ============================================================
  # Private Helpers
  # ============================================================

  defp unit_to_ms("ms"), do: 1
  defp unit_to_ms("s"), do: 1_000
  defp unit_to_ms("m"), do: 60_000
  defp unit_to_ms("h"), do: 3_600_000
  defp unit_to_ms("d"), do: 86_400_000
  defp unit_to_ms("w"), do: 604_800_000

  defp parse_days("all"), do: {:ok, :all}
  defp parse_days("weekdays"), do: {:ok, :weekdays}
  defp parse_days("weekend"), do: {:ok, :weekend}
  defp parse_days("everyday"), do: {:ok, :all}

  defp parse_days(str) do
    days = str
      |> String.downcase()
      |> String.split(",")
      |> Enum.map(&day_to_number/1)

    if Enum.all?(days, & &1 != nil) do
      {:ok, days}
    else
      {:error, :invalid_days}
    end
  end

  defp day_to_number("monday"), do: 1
  defp day_to_number("mon"), do: 1
  defp day_to_number("tuesday"), do: 2
  defp day_to_number("tue"), do: 2
  defp day_to_number("wednesday"), do: 3
  defp day_to_number("wed"), do: 3
  defp day_to_number("thursday"), do: 4
  defp day_to_number("thu"), do: 4
  defp day_to_number("friday"), do: 5
  defp day_to_number("fri"), do: 5
  defp day_to_number("saturday"), do: 6
  defp day_to_number("sat"), do: 6
  defp day_to_number("sunday"), do: 7
  defp day_to_number("sun"), do: 7
  defp day_to_number(_), do: nil

  defp find_next_match(_dt, _schedule, minutes) when minutes > 60 * 24 * 7 do
    :never
  end

  defp find_next_match(dt, schedule, minutes) do
    next_dt = DateTime.add(dt, minutes, :minute)

    if matches_schedule?(next_dt, schedule) do
      minutes * 60_000
    else
      find_next_match(dt, schedule, minutes + 1)
    end
  end
end
