# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.PackageManager.Manifest do
  @moduledoc """
  Manifest file parsing and writing for Phronesis packages.

  Handles phronesis.ncl files in Nickel format.
  """

  @doc """
  Read and parse a manifest file.
  """
  def read(path) do
    with {:ok, content} <- File.read(path),
         {:ok, manifest} <- parse(content) do
      {:ok, manifest}
    end
  end

  @doc """
  Write a manifest to a file.
  """
  def write(manifest, path) do
    content = format(manifest)
    File.write(path, content)
  end

  @doc """
  Parse a Nickel manifest string.

  For now, uses a simplified parser. In production, would use
  actual Nickel parser.
  """
  def parse(content) do
    # Simplified parser - in production would use actual Nickel parser
    # For now, parse as a simple key-value format

    manifest = %{
      name: extract_field(content, "name"),
      version: extract_field(content, "version"),
      description: extract_field(content, "description", ""),
      dependencies: extract_dependencies(content),
      policies: extract_policies(content)
    }

    {:ok, manifest}
  rescue
    _ -> {:error, :parse_error}
  end

  @doc """
  Format a manifest as Nickel.
  """
  def format(manifest) do
    deps =
      if map_size(manifest.dependencies) > 0 do
        dep_entries =
          manifest.dependencies
          |> Enum.map(fn {name, version} -> "    #{name} = \"#{version}\"" end)
          |> Enum.join(",\n")

        "  dependencies = {\n#{dep_entries}\n  },\n"
      else
        "  dependencies = {},\n"
      end

    policies =
      if length(manifest.policies) > 0 do
        policy_entries =
          manifest.policies
          |> Enum.map(&"    \"#{&1}\"")
          |> Enum.join(",\n")

        "  policies = [\n#{policy_entries}\n  ]\n"
      else
        "  policies = []\n"
      end

    """
    # Phronesis package manifest
    {
      name = "#{manifest.name}",
      version = "#{manifest.version}",
      description = "#{manifest.description}",
    #{deps}#{policies}}
    """
  end

  ## Private Helpers

  defp extract_field(content, field, default \\ nil) do
    # Simple regex extraction - in production would use proper Nickel parser
    regex = ~r/#{field}\s*=\s*"([^"]+)"/

    case Regex.run(regex, content) do
      [_, value] -> value
      nil -> default
    end
  end

  defp extract_dependencies(content) do
    # Extract dependencies block
    case Regex.run(~r/dependencies\s*=\s*\{([^}]*)\}/s, content) do
      [_, deps_block] ->
        # Parse individual dependencies
        ~r/(\w+)\s*=\s*"([^"]+)"/
        |> Regex.scan(deps_block)
        |> Enum.map(fn [_, name, version] -> {name, version} end)
        |> Map.new()

      nil ->
        %{}
    end
  end

  defp extract_policies(content) do
    # Extract policies array
    case Regex.run(~r/policies\s*=\s*\[([^\]]*)\]/s, content) do
      [_, policies_block] ->
        ~r/"([^"]+)"/
        |> Regex.scan(policies_block)
        |> Enum.map(fn [_, policy] -> policy end)

      nil ->
        []
    end
  end
end
