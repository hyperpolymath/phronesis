# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Library.Common.Validation do
  @moduledoc """
  Common validation utilities for network policy languages.

  Provides type checking, constraint validation, and schema validation
  that can be reused across different network policy DSLs.
  """

  alias Phronesis.Library.Common.Network

  # ============================================================
  # Type Validation
  # ============================================================

  @doc """
  Validate a value against a type specification.
  """
  @spec validate_type(any(), atom() | {atom(), any()}) :: :ok | {:error, String.t()}
  def validate_type(value, :string) when is_binary(value), do: :ok
  def validate_type(value, :integer) when is_integer(value), do: :ok
  def validate_type(value, :float) when is_float(value), do: :ok
  def validate_type(value, :number) when is_number(value), do: :ok
  def validate_type(value, :boolean) when is_boolean(value), do: :ok
  def validate_type(value, :atom) when is_atom(value), do: :ok
  def validate_type(value, :list) when is_list(value), do: :ok
  def validate_type(value, :map) when is_map(value), do: :ok

  def validate_type(value, :ipv4) when is_binary(value) do
    case Network.parse_ipv4(value) do
      {:ok, _} -> :ok
      _ -> {:error, "invalid IPv4 address: #{value}"}
    end
  end

  def validate_type(value, :ipv6) when is_binary(value) do
    case Network.parse_ipv6(value) do
      {:ok, _} -> :ok
      _ -> {:error, "invalid IPv6 address: #{value}"}
    end
  end

  def validate_type(value, :ip) when is_binary(value) do
    case {Network.parse_ipv4(value), Network.parse_ipv6(value)} do
      {{:ok, _}, _} -> :ok
      {_, {:ok, _}} -> :ok
      _ -> {:error, "invalid IP address: #{value}"}
    end
  end

  def validate_type(value, :cidr) when is_binary(value) do
    case Network.parse_cidr(value) do
      {:ok, _, _} -> :ok
      _ -> {:error, "invalid CIDR: #{value}"}
    end
  end

  def validate_type(value, :port) when is_integer(value) do
    if Network.valid_port?(value) do
      :ok
    else
      {:error, "invalid port: #{value} (must be 0-65535)"}
    end
  end

  def validate_type(value, :asn) when is_integer(value) do
    if value >= 0 and value <= 4_294_967_295 do
      :ok
    else
      {:error, "invalid ASN: #{value}"}
    end
  end

  def validate_type(value, {:list, elem_type}) when is_list(value) do
    errors = value
      |> Enum.with_index()
      |> Enum.filter(fn {elem, _} -> validate_type(elem, elem_type) != :ok end)
      |> Enum.map(fn {elem, idx} -> "element #{idx}: #{inspect(elem)}" end)

    if errors == [] do
      :ok
    else
      {:error, "invalid list elements: #{Enum.join(errors, ", ")}"}
    end
  end

  def validate_type(value, {:one_of, values}) do
    if value in values do
      :ok
    else
      {:error, "value must be one of: #{inspect(values)}"}
    end
  end

  def validate_type(value, type) do
    {:error, "#{inspect(value)} is not a valid #{type}"}
  end

  # ============================================================
  # Constraint Validation
  # ============================================================

  @doc """
  Validate a value against constraints.
  """
  @spec validate_constraints(any(), keyword()) :: :ok | {:error, String.t()}
  def validate_constraints(value, constraints) do
    Enum.reduce_while(constraints, :ok, fn constraint, _acc ->
      case validate_constraint(value, constraint) do
        :ok -> {:cont, :ok}
        error -> {:halt, error}
      end
    end)
  end

  defp validate_constraint(value, {:min, min}) when is_number(value) do
    if value >= min, do: :ok, else: {:error, "value must be >= #{min}"}
  end

  defp validate_constraint(value, {:max, max}) when is_number(value) do
    if value <= max, do: :ok, else: {:error, "value must be <= #{max}"}
  end

  defp validate_constraint(value, {:min_length, min}) when is_binary(value) do
    if String.length(value) >= min do
      :ok
    else
      {:error, "string length must be >= #{min}"}
    end
  end

  defp validate_constraint(value, {:max_length, max}) when is_binary(value) do
    if String.length(value) <= max do
      :ok
    else
      {:error, "string length must be <= #{max}"}
    end
  end

  defp validate_constraint(value, {:min_length, min}) when is_list(value) do
    if length(value) >= min do
      :ok
    else
      {:error, "list length must be >= #{min}"}
    end
  end

  defp validate_constraint(value, {:max_length, max}) when is_list(value) do
    if length(value) <= max do
      :ok
    else
      {:error, "list length must be <= #{max}"}
    end
  end

  defp validate_constraint(value, {:pattern, regex}) when is_binary(value) do
    if Regex.match?(regex, value) do
      :ok
    else
      {:error, "value does not match pattern"}
    end
  end

  defp validate_constraint(value, {:in, allowed}) do
    if value in allowed do
      :ok
    else
      {:error, "value must be one of: #{inspect(allowed)}"}
    end
  end

  defp validate_constraint(value, {:not_in, disallowed}) do
    if value not in disallowed do
      :ok
    else
      {:error, "value must not be one of: #{inspect(disallowed)}"}
    end
  end

  defp validate_constraint(_value, {constraint, _}) do
    {:error, "unknown constraint: #{constraint}"}
  end

  # ============================================================
  # Schema Validation
  # ============================================================

  @doc """
  Validate a map against a schema.

  Schema format:
    %{
      field_name: %{type: :type, required: bool, constraints: [...]}
    }
  """
  @spec validate_schema(map(), map()) :: :ok | {:error, [{atom(), String.t()}]}
  def validate_schema(data, schema) when is_map(data) and is_map(schema) do
    errors = Enum.flat_map(schema, fn {field, spec} ->
      validate_field(data, field, spec)
    end)

    # Check for unknown fields
    unknown = Map.keys(data) -- Map.keys(schema)
    unknown_errors = Enum.map(unknown, fn field ->
      {field, "unknown field"}
    end)

    all_errors = errors ++ unknown_errors

    if all_errors == [] do
      :ok
    else
      {:error, all_errors}
    end
  end

  defp validate_field(data, field, spec) do
    value = Map.get(data, field)
    required = Map.get(spec, :required, false)
    type = Map.get(spec, :type)
    constraints = Map.get(spec, :constraints, [])

    cond do
      value == nil and required ->
        [{field, "required field missing"}]

      value == nil ->
        []

      type != nil ->
        case validate_type(value, type) do
          :ok ->
            case validate_constraints(value, constraints) do
              :ok -> []
              {:error, msg} -> [{field, msg}]
            end

          {:error, msg} ->
            [{field, msg}]
        end

      true ->
        case validate_constraints(value, constraints) do
          :ok -> []
          {:error, msg} -> [{field, msg}]
        end
    end
  end

  # ============================================================
  # Network-Specific Validators
  # ============================================================

  @doc """
  Validate BGP route announcement parameters.
  """
  @spec validate_route_announcement(map()) :: :ok | {:error, term()}
  def validate_route_announcement(route) do
    schema = %{
      prefix: %{type: :cidr, required: true},
      next_hop: %{type: :ip, required: true},
      as_path: %{type: {:list, :asn}, required: false},
      local_pref: %{type: :integer, constraints: [min: 0, max: 4_294_967_295]},
      med: %{type: :integer, constraints: [min: 0, max: 4_294_967_295]},
      communities: %{type: {:list, :string}}
    }

    validate_schema(route, schema)
  end

  @doc """
  Validate firewall rule parameters.
  """
  @spec validate_firewall_rule(map()) :: :ok | {:error, term()}
  def validate_firewall_rule(rule) do
    schema = %{
      action: %{type: {:one_of, [:accept, :drop, :reject]}, required: true},
      protocol: %{type: {:one_of, [:tcp, :udp, :icmp, :any]}},
      src_ip: %{type: :cidr},
      dst_ip: %{type: :cidr},
      src_port: %{type: :port},
      dst_port: %{type: :port}
    }

    validate_schema(rule, schema)
  end
end
