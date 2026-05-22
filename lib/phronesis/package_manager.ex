# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.PackageManager do
  @moduledoc """
  Package manager for Phronesis policy libraries.

  Provides dependency resolution, version management, and package installation
  for reusable policy libraries.

  ## Usage

      # Initialize a new package
      PackageManager.init("my-policies")

      # Install dependencies
      PackageManager.install("acme-common")

      # List installed packages
      PackageManager.list()

  ## Manifest Format

  Packages are defined in `phronesis.ncl` using Nickel:

      {
        name = "acme-network-policies",
        version = "1.0.0",
        description = "Network security policies for ACME Corp",
        dependencies = {
          std = "^0.2.0",
          acme-common = "^2.1.0"
        },
        policies = [
          "bgp_security.phr",
          "rpki_validation.phr"
        ]
      }

  ## Version Constraints

  Supports semantic versioning with constraints:
  - `^1.2.3` - Compatible with 1.2.3, allows 1.x.x
  - `~1.2.3` - Compatible with 1.2.3, allows 1.2.x
  - `>=1.0.0` - Greater than or equal to 1.0.0
  - `1.2.3` - Exact version match
  """

  alias Phronesis.PackageManager.{Manifest, Resolver, Registry}

  @packages_dir ".phronesis/packages"
  @manifest_file "phronesis.ncl"

  ## Public API

  @doc """
  Initialize a new package in the current directory.
  """
  def init(name, opts \\ []) do
    version = Keyword.get(opts, :version, "0.1.0")
    description = Keyword.get(opts, :description, "")

    manifest = %{
      name: name,
      version: version,
      description: description,
      dependencies: %{},
      policies: []
    }

    case Manifest.write(manifest, @manifest_file) do
      :ok ->
        IO.puts("Initialized package: #{name} v#{version}")
        IO.puts("Created #{@manifest_file}")
        {:ok, manifest}

      {:error, reason} ->
        {:error, reason}
    end
  end

  @doc """
  Install a package and its dependencies.
  """
  def install(package_spec, opts \\ []) do
    with {:ok, manifest} <- load_manifest(),
         {:ok, package_info} <- parse_package_spec(package_spec),
         {:ok, resolved} <- resolve_dependencies(package_info, manifest) do
      # Install all resolved packages
      results =
        Enum.map(resolved, fn {pkg_name, version} ->
          install_package(pkg_name, version, opts)
        end)

      # Check for errors
      errors = Enum.filter(results, &match?({:error, _}, &1))

      if Enum.empty?(errors) do
        IO.puts("\n✓ Successfully installed #{length(resolved)} package(s)")
        {:ok, resolved}
      else
        {:error, {:install_failed, errors}}
      end
    end
  end

  @doc """
  List all installed packages.
  """
  def list do
    packages_path = Path.join(File.cwd!(), @packages_dir)

    if File.dir?(packages_path) do
      packages =
        File.ls!(packages_path)
        |> Enum.filter(&File.dir?(Path.join(packages_path, &1)))
        |> Enum.map(fn pkg_name ->
          pkg_path = Path.join([packages_path, pkg_name])
          manifest_path = Path.join(pkg_path, @manifest_file)

          case Manifest.read(manifest_path) do
            {:ok, manifest} ->
              {pkg_name, manifest.version, manifest.description}

            {:error, _} ->
              {pkg_name, "unknown", ""}
          end
        end)
        |> Enum.sort()

      {:ok, packages}
    else
      {:ok, []}
    end
  end

  @doc """
  Show information about an installed package.
  """
  def show(package_name) do
    pkg_path = Path.join([File.cwd!(), @packages_dir, package_name])
    manifest_path = Path.join(pkg_path, @manifest_file)

    case Manifest.read(manifest_path) do
      {:ok, manifest} ->
        {:ok, manifest}

      {:error, :enoent} ->
        {:error, {:package_not_found, package_name}}

      {:error, reason} ->
        {:error, reason}
    end
  end

  ## Private Functions

  defp load_manifest do
    case Manifest.read(@manifest_file) do
      {:ok, manifest} ->
        {:ok, manifest}

      {:error, :enoent} ->
        {:error, :no_manifest}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_package_spec(spec) do
    case String.split(spec, "@", parts: 2) do
      [name, version] ->
        {:ok, %{name: name, version: version}}

      [name] ->
        {:ok, %{name: name, version: "latest"}}
    end
  end

  defp resolve_dependencies(package_info, _manifest) do
    # For now, simple resolution without transitive dependencies
    # In a full implementation, this would recursively resolve all dependencies
    resolved = [{package_info.name, package_info.version}]
    {:ok, resolved}
  end

  defp install_package(name, version, opts) do
    verbose = Keyword.get(opts, :verbose, false)

    if verbose do
      IO.puts("Installing #{name}@#{version}...")
    end

    # Try to fetch from registry
    case Registry.fetch(name, version) do
      {:ok, package_data} ->
        install_path = Path.join([File.cwd!(), @packages_dir, name])
        File.mkdir_p!(install_path)

        # Write package files
        Enum.each(package_data.files, fn {file_path, content} ->
          full_path = Path.join(install_path, file_path)
          File.mkdir_p!(Path.dirname(full_path))
          File.write!(full_path, content)
        end)

        # Write manifest
        manifest_path = Path.join(install_path, @manifest_file)
        Manifest.write(package_data.manifest, manifest_path)

        IO.puts("  ✓ #{name}@#{version}")
        {:ok, name}

      {:error, :not_found} ->
        IO.puts(:stderr, "  ✗ #{name}@#{version} - not found in registry")
        {:error, {:not_found, name, version}}

      {:error, reason} ->
        IO.puts(:stderr, "  ✗ #{name}@#{version} - #{inspect(reason)}")
        {:error, reason}
    end
  end

  ## Formatting

  @doc """
  Format package list for display.
  """
  def format_list(packages) do
    if Enum.empty?(packages) do
      "No packages installed"
    else
      header = "Installed packages:\n"

      rows =
        Enum.map_join(packages, "\n", fn {name, version, description} ->
          desc_text = if description != "", do: " - #{description}", else: ""
          "  #{name}@#{version}#{desc_text}"
        end)

      header <> rows
    end
  end

  @doc """
  Format package info for display.
  """
  def format_info(manifest) do
    """
    Package: #{manifest.name}
    Version: #{manifest.version}
    Description: #{manifest.description}

    Dependencies:
    #{format_dependencies(manifest.dependencies)}

    Policies:
    #{format_policies(manifest.policies)}
    """
  end

  defp format_dependencies(deps) when map_size(deps) == 0, do: "  (none)"

  defp format_dependencies(deps) do
    deps
    |> Enum.map(fn {name, version} -> "  #{name}@#{version}" end)
    |> Enum.join("\n")
  end

  defp format_policies(policies) when policies == [], do: "  (none)"

  defp format_policies(policies) do
    policies
    |> Enum.map(&"  #{&1}")
    |> Enum.join("\n")
  end
end
