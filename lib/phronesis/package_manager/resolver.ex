# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.PackageManager.Resolver do
  @moduledoc """
  Dependency resolution with semantic versioning support.

  Resolves package dependencies and handles version constraints.
  """

  @doc """
  Resolve dependencies for a package.

  Returns a list of {package_name, version} tuples representing
  all packages that need to be installed.
  """
  def resolve(package_name, version_constraint, opts \\ []) do
    registry = Keyword.get(opts, :registry, Phronesis.PackageManager.Registry)

    with {:ok, versions} <- registry.list_versions(package_name),
         {:ok, selected_version} <- select_version(versions, version_constraint) do
      {:ok, [{package_name, selected_version}]}
    end
  end

  @doc """
  Select the best matching version from available versions.
  """
  def select_version(available_versions, constraint) do
    matching =
      available_versions
      |> Enum.filter(&matches_constraint?(&1, constraint))
      |> Enum.sort(fn v1, v2 -> version_compare(v1, v2) == :lt end)

    case List.last(matching) do
      nil -> {:error, {:no_matching_version, constraint}}
      version -> {:ok, version}
    end
  end

  @doc """
  Check if a version matches a constraint.

  Supports:
  - Exact: "1.2.3"
  - Caret: "^1.2.3" (compatible, allows 1.x.x)
  - Tilde: "~1.2.3" (compatible, allows 1.2.x)
  - Greater/less: ">=1.0.0", ">1.0.0", "<=2.0.0", "<2.0.0"
  - Latest: "latest"
  """
  def matches_constraint?(version, "latest"), do: true

  def matches_constraint?(version, "^" <> base) do
    {major, _, _} = parse_version(base)
    {v_major, _, _} = parse_version(version)

    v_major == major and version_compare(version, base) in [:gt, :eq]
  end

  def matches_constraint?(version, "~" <> base) do
    {major, minor, _} = parse_version(base)
    {v_major, v_minor, _} = parse_version(version)

    v_major == major and v_minor == minor and version_compare(version, base) in [:gt, :eq]
  end

  def matches_constraint?(version, ">=" <> base) do
    version_compare(version, base) in [:gt, :eq]
  end

  def matches_constraint?(version, ">" <> base) do
    version_compare(version, base) == :gt
  end

  def matches_constraint?(version, "<=" <> base) do
    version_compare(version, base) in [:lt, :eq]
  end

  def matches_constraint?(version, "<" <> base) do
    version_compare(version, base) == :lt
  end

  def matches_constraint?(version, exact) do
    version == exact
  end

  @doc """
  Compare two semantic versions.

  Returns :gt, :lt, or :eq.
  """
  def version_compare(v1, v2) do
    {major1, minor1, patch1} = parse_version(v1)
    {major2, minor2, patch2} = parse_version(v2)

    cond do
      major1 > major2 -> :gt
      major1 < major2 -> :lt
      minor1 > minor2 -> :gt
      minor1 < minor2 -> :lt
      patch1 > patch2 -> :gt
      patch1 < patch2 -> :lt
      true -> :eq
    end
  end

  @doc """
  Parse a semantic version string into {major, minor, patch}.
  """
  def parse_version(version) do
    case String.split(version, ".") do
      [major, minor, patch] ->
        {String.to_integer(major), String.to_integer(minor), String.to_integer(patch)}

      [major, minor] ->
        {String.to_integer(major), String.to_integer(minor), 0}

      [major] ->
        {String.to_integer(major), 0, 0}

      _ ->
        {0, 0, 0}
    end
  end

  @doc """
  Format a version tuple as a string.
  """
  def format_version({major, minor, patch}) do
    "#{major}.#{minor}.#{patch}"
  end
end
