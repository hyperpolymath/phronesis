# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.PackageManager.Registry do
  @moduledoc """
  Local package registry for Phronesis packages.

  Manages a local cache of available packages and their metadata.
  In production, this would connect to a remote registry.
  """

  @registry_dir ".phronesis/registry"
  @index_file ".phronesis/registry/index.json"

  @doc """
  Initialize the local registry.
  """
  def init do
    File.mkdir_p!(@registry_dir)

    unless File.exists?(@index_file) do
      initial_index = %{
        "packages" => %{},
        "updated_at" => DateTime.utc_now() |> DateTime.to_iso8601()
      }

      write_index(initial_index)
    end

    :ok
  end

  @doc """
  Add a package to the registry.
  """
  def add(package_name, version, package_data) do
    init()
    index = read_index()

    # Create package entry if it doesn't exist
    packages = Map.get(index, "packages", %{})

    package_versions =
      packages
      |> Map.get(package_name, %{})
      |> Map.put(version, package_metadata(package_data))

    updated_packages = Map.put(packages, package_name, package_versions)

    updated_index =
      index
      |> Map.put("packages", updated_packages)
      |> Map.put("updated_at", DateTime.utc_now() |> DateTime.to_iso8601())

    # Write package files
    pkg_dir = Path.join([@registry_dir, package_name, version])
    File.mkdir_p!(pkg_dir)

    Enum.each(package_data.files, fn {file_path, content} ->
      full_path = Path.join(pkg_dir, file_path)
      File.mkdir_p!(Path.dirname(full_path))
      File.write!(full_path, content)
    end)

    # Write manifest
    manifest_path = Path.join(pkg_dir, "phronesis.ncl")
    Phronesis.PackageManager.Manifest.write(package_data.manifest, manifest_path)

    write_index(updated_index)
    {:ok, package_name}
  end

  @doc """
  Fetch a package from the registry.
  """
  def fetch(package_name, version) do
    version = if version == "latest", do: get_latest_version(package_name), else: version

    case version do
      nil ->
        {:error, :not_found}

      ver ->
        pkg_dir = Path.join([@registry_dir, package_name, ver])

        if File.dir?(pkg_dir) do
          manifest_path = Path.join(pkg_dir, "phronesis.ncl")

          case Phronesis.PackageManager.Manifest.read(manifest_path) do
            {:ok, manifest} ->
              files = collect_package_files(pkg_dir)
              {:ok, %{manifest: manifest, files: files}}

            error ->
              error
          end
        else
          {:error, :not_found}
        end
    end
  end

  @doc """
  List all versions of a package.
  """
  def list_versions(package_name) do
    index = read_index()
    packages = Map.get(index, "packages", %{})

    case Map.get(packages, package_name) do
      nil ->
        {:ok, []}

      versions ->
        version_list =
          versions
          |> Map.keys()
          |> Enum.sort()

        {:ok, version_list}
    end
  end

  @doc """
  List all packages in the registry.
  """
  def list_packages do
    index = read_index()
    packages = Map.get(index, "packages", %{})

    package_list =
      Enum.map(packages, fn {name, versions} ->
        latest = get_latest_version_from_map(versions)
        {name, latest, Map.keys(versions)}
      end)

    {:ok, package_list}
  end

  @doc """
  Search for packages by name pattern.
  """
  def search(pattern) do
    {:ok, packages} = list_packages()

    matching =
      Enum.filter(packages, fn {name, _latest, _versions} ->
        String.contains?(String.downcase(name), String.downcase(pattern))
      end)

    {:ok, matching}
  end

  ## Private Functions

  defp read_index do
    case File.read(@index_file) do
      {:ok, content} ->
        Jason.decode!(content)

      {:error, _} ->
        %{"packages" => %{}}
    end
  end

  defp write_index(index) do
    content = Jason.encode!(index, pretty: true)
    File.write!(@index_file, content)
  end

  defp package_metadata(package_data) do
    %{
      "description" => package_data.manifest.description,
      "policies" => package_data.manifest.policies,
      "dependencies" => package_data.manifest.dependencies
    }
  end

  defp get_latest_version(package_name) do
    case list_versions(package_name) do
      {:ok, []} -> nil
      {:ok, versions} -> List.last(Enum.sort(versions))
    end
  end

  defp get_latest_version_from_map(versions) when map_size(versions) == 0, do: nil

  defp get_latest_version_from_map(versions) do
    versions
    |> Map.keys()
    |> Enum.sort()
    |> List.last()
  end

  defp collect_package_files(pkg_dir) do
    pkg_dir
    |> Path.join("**/*")
    |> Path.wildcard()
    |> Enum.reject(&File.dir?/1)
    |> Enum.map(fn file ->
      relative = Path.relative_to(file, pkg_dir)
      content = File.read!(file)
      {relative, content}
    end)
  end
end
