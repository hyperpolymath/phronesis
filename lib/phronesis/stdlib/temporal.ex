# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Stdlib.Temporal do
  @moduledoc """
  Temporal functions for time-based policy evaluation.

  Provides utilities for working with timestamps, durations, and time windows
  in policy conditions.

  ## Examples

      Temporal.now()
      #=> ~U[2025-01-30 20:00:00Z]

      Temporal.is_expired(~U[2025-01-01 00:00:00Z], 3600)
      #=> true

      Temporal.within_window(~U[2025-01-30 09:00:00Z], ~U[2025-01-30 17:00:00Z])
      #=> true (if current time is between 9am and 5pm)
  """

  @doc """
  Get the current UTC timestamp.

  ## Returns

  Current time as a DateTime struct in UTC.

  ## Examples

      iex> now()
      ~U[2025-01-30 20:15:30.123456Z]
  """
  @spec now() :: DateTime.t()
  def now do
    DateTime.utc_now()
  end

  @doc """
  Check if a timestamp has expired relative to current time.

  ## Parameters

  - `timestamp` - The timestamp to check (DateTime or Unix timestamp)
  - `duration_seconds` - How many seconds until expiration

  ## Returns

  `true` if `now() > timestamp + duration_seconds`, `false` otherwise

  ## Examples

      iex> past = DateTime.add(DateTime.utc_now(), -7200, :second)
      iex> is_expired(past, 3600)
      true  # Expired 1 hour ago

      iex> future = DateTime.add(DateTime.utc_now(), 7200, :second)
      iex> is_expired(future, 3600)
      false  # Won't expire for another hour
  """
  @spec is_expired(DateTime.t() | integer(), integer()) :: boolean()
  def is_expired(%DateTime{} = timestamp, duration_seconds) when is_integer(duration_seconds) do
    expiration = DateTime.add(timestamp, duration_seconds, :second)
    DateTime.compare(DateTime.utc_now(), expiration) == :gt
  end

  def is_expired(unix_timestamp, duration_seconds) when is_integer(unix_timestamp) and is_integer(duration_seconds) do
    case DateTime.from_unix(unix_timestamp) do
      {:ok, dt} -> is_expired(dt, duration_seconds)
      {:error, _} -> false
    end
  end

  @doc """
  Check if current time is within a time window.

  ## Parameters

  - `start_time` - Window start (DateTime or ISO8601 string)
  - `end_time` - Window end (DateTime or ISO8601 string)

  ## Returns

  `true` if `start_time <= now() <= end_time`, `false` otherwise

  ## Examples

      iex> start = ~U[2025-01-30 09:00:00Z]
      iex> end_time = ~U[2025-01-30 17:00:00Z]
      iex> within_window(start, end_time)
      true  # If current time is between 9am and 5pm UTC
  """
  @spec within_window(DateTime.t() | String.t(), DateTime.t() | String.t()) :: boolean()
  def within_window(%DateTime{} = start_time, %DateTime{} = end_time) do
    now = DateTime.utc_now()
    DateTime.compare(now, start_time) != :lt and DateTime.compare(now, end_time) != :gt
  end

  def within_window(start_str, end_str) when is_binary(start_str) and is_binary(end_str) do
    with {:ok, start_time, _} <- DateTime.from_iso8601(start_str),
         {:ok, end_time, _} <- DateTime.from_iso8601(end_str) do
      within_window(start_time, end_time)
    else
      _ -> false
    end
  end

  @doc """
  Parse an ISO8601 timestamp string to DateTime.

  ## Examples

      iex> parse("2025-01-30T20:00:00Z")
      {:ok, ~U[2025-01-30 20:00:00Z]}

      iex> parse("invalid")
      {:error, :invalid_format}
  """
  @spec parse(String.t()) :: {:ok, DateTime.t()} | {:error, atom()}
  def parse(timestamp_str) when is_binary(timestamp_str) do
    case DateTime.from_iso8601(timestamp_str) do
      {:ok, dt, _offset} -> {:ok, dt}
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Format a DateTime as an ISO8601 string.

  ## Examples

      iex> dt = ~U[2025-01-30 20:00:00Z]
      iex> format(dt)
      "2025-01-30T20:00:00Z"
  """
  @spec format(DateTime.t()) :: String.t()
  def format(%DateTime{} = dt) do
    DateTime.to_iso8601(dt)
  end

  @doc """
  Calculate duration between two timestamps in seconds.

  ## Examples

      iex> start = ~U[2025-01-30 20:00:00Z]
      iex> end_time = ~U[2025-01-30 21:00:00Z]
      iex> duration(start, end_time)
      3600
  """
  @spec duration(DateTime.t(), DateTime.t()) :: integer()
  def duration(%DateTime{} = start_time, %DateTime{} = end_time) do
    DateTime.diff(end_time, start_time, :second)
  end

  @doc """
  Get Unix timestamp (seconds since epoch) for a DateTime.

  ## Examples

      iex> dt = ~U[2025-01-30 20:00:00Z]
      iex> to_unix(dt)
      1738267200
  """
  @spec to_unix(DateTime.t()) :: integer()
  def to_unix(%DateTime{} = dt) do
    DateTime.to_unix(dt)
  end

  @doc """
  Convert Unix timestamp to DateTime.

  ## Examples

      iex> from_unix(1738267200)
      {:ok, ~U[2025-01-30 20:00:00Z]}
  """
  @spec from_unix(integer()) :: {:ok, DateTime.t()} | {:error, atom()}
  def from_unix(unix_timestamp) when is_integer(unix_timestamp) do
    DateTime.from_unix(unix_timestamp)
  end
end
