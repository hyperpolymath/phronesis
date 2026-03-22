# SPDX-License-Identifier: PMPL-1.0-or-later
defmodule Phronesis.PackageManagerTest do
  use ExUnit.Case, async: false
  alias Phronesis.PackageManager
  alias Phronesis.PackageManager.{Manifest, Resolver, Registry}

  @test_dir "/tmp/phronesis_pkg_test_#{System.unique_integer()}"

  setup do
    # Create test directory and change to it
    File.mkdir_p!(@test_dir)
    original_dir = File.cwd!()
    File.cd!(@test_dir)

    on_exit(fn ->
      File.cd!(original_dir)
      File.rm_rf!(@test_dir)
    end)

    :ok
  end

  describe "Manifest" do
    test "writes and reads manifest files" do
      manifest = %{
        name: "test-package",
        version: "1.0.0",
        description: "Test package",
        dependencies: %{"foo" => "^1.0.0"},
        policies: ["test.phr"]
      }

      assert :ok = Manifest.write(manifest, "test.ncl")
      assert {:ok, read_manifest} = Manifest.read("test.ncl")

      assert read_manifest.name == "test-package"
      assert read_manifest.version == "1.0.0"
      assert read_manifest.description == "Test package"
      assert read_manifest.dependencies == %{"foo" => "^1.0.0"}
      assert read_manifest.policies == ["test.phr"]
    end

    test "formats manifest as Nickel" do
      manifest = %{
        name: "test-pkg",
        version: "0.1.0",
        description: "Test",
        dependencies: %{},
        policies: []
      }

      formatted = Manifest.format(manifest)

      assert formatted =~ "name = \"test-pkg\""
      assert formatted =~ "version = \"0.1.0\""
      assert formatted =~ "description = \"Test\""
    end

    test "parses dependencies correctly" do
      content = """
      {
        name = "test",
        version = "1.0.0",
        description = "Test package",
        dependencies = {
          foo = "^1.0.0",
          bar = "~2.1.0"
        },
        policies = []
      }
      """

      {:ok, manifest} = Manifest.parse(content)

      assert manifest.dependencies == %{"foo" => "^1.0.0", "bar" => "~2.1.0"}
    end

    test "parses policies correctly" do
      content = """
      {
        name = "test",
        version = "1.0.0",
        description = "",
        dependencies = {},
        policies = [
          "policy1.phr",
          "policy2.phr"
        ]
      }
      """

      {:ok, manifest} = Manifest.parse(content)

      assert manifest.policies == ["policy1.phr", "policy2.phr"]
    end
  end

  describe "Resolver" do
    test "parses semantic versions" do
      assert {1, 2, 3} = Resolver.parse_version("1.2.3")
      assert {1, 2, 0} = Resolver.parse_version("1.2")
      assert {1, 0, 0} = Resolver.parse_version("1")
    end

    test "compares versions correctly" do
      assert Resolver.version_compare("1.2.3", "1.2.2") == :gt
      assert Resolver.version_compare("1.2.2", "1.2.3") == :lt
      assert Resolver.version_compare("1.2.3", "1.2.3") == :eq
      assert Resolver.version_compare("2.0.0", "1.9.9") == :gt
    end

    test "matches caret constraints" do
      assert Resolver.matches_constraint?("1.2.3", "^1.0.0")
      assert Resolver.matches_constraint?("1.9.9", "^1.0.0")
      refute Resolver.matches_constraint?("2.0.0", "^1.0.0")
      refute Resolver.matches_constraint?("0.9.9", "^1.0.0")
    end

    test "matches tilde constraints" do
      assert Resolver.matches_constraint?("1.2.3", "~1.2.0")
      assert Resolver.matches_constraint?("1.2.9", "~1.2.0")
      refute Resolver.matches_constraint?("1.3.0", "~1.2.0")
      refute Resolver.matches_constraint?("1.1.9", "~1.2.0")
    end

    test "matches greater than or equal constraints" do
      assert Resolver.matches_constraint?("1.2.3", ">=1.0.0")
      assert Resolver.matches_constraint?("1.0.0", ">=1.0.0")
      assert Resolver.matches_constraint?("2.0.0", ">=1.0.0")
      refute Resolver.matches_constraint?("0.9.9", ">=1.0.0")
    end

    test "matches greater than constraints" do
      assert Resolver.matches_constraint?("1.2.3", ">1.0.0")
      refute Resolver.matches_constraint?("1.0.0", ">1.0.0")
      assert Resolver.matches_constraint?("2.0.0", ">1.0.0")
      refute Resolver.matches_constraint?("0.9.9", ">1.0.0")
    end

    test "matches exact constraints" do
      assert Resolver.matches_constraint?("1.2.3", "1.2.3")
      refute Resolver.matches_constraint?("1.2.4", "1.2.3")
      refute Resolver.matches_constraint?("1.2.2", "1.2.3")
    end

    test "matches latest" do
      assert Resolver.matches_constraint?("1.2.3", "latest")
      assert Resolver.matches_constraint?("0.0.1", "latest")
    end

    test "selects best matching version" do
      versions = ["1.0.0", "1.1.0", "1.2.0", "2.0.0"]

      {:ok, selected} = Resolver.select_version(versions, "^1.0.0")
      assert selected == "1.2.0"

      {:ok, selected} = Resolver.select_version(versions, "~1.1.0")
      assert selected == "1.1.0"

      {:ok, selected} = Resolver.select_version(versions, ">=2.0.0")
      assert selected == "2.0.0"
    end

    test "returns error when no version matches" do
      versions = ["1.0.0", "1.1.0"]

      assert {:error, {:no_matching_version, ">=2.0.0"}} =
               Resolver.select_version(versions, ">=2.0.0")
    end
  end

  describe "Registry" do
    test "initializes registry" do
      assert :ok = Registry.init()
      assert File.exists?(".phronesis/registry/index.json")
    end

    test "adds and fetches packages" do
      Registry.init()

      package_data = %{
        manifest: %{
          name: "test-pkg",
          version: "1.0.0",
          description: "Test package",
          dependencies: %{},
          policies: []
        },
        files: [
          {"test.phr", "# Test policy"}
        ]
      }

      assert {:ok, "test-pkg"} = Registry.add("test-pkg", "1.0.0", package_data)
      assert {:ok, fetched} = Registry.fetch("test-pkg", "1.0.0")

      assert fetched.manifest.name == "test-pkg"
      assert fetched.manifest.version == "1.0.0"
    end

    test "lists package versions" do
      Registry.init()

      package_data = %{
        manifest: %{name: "test", version: "1.0.0", description: "", dependencies: %{}, policies: []},
        files: []
      }

      Registry.add("test", "1.0.0", package_data)
      Registry.add("test", "1.1.0", %{package_data | manifest: %{package_data.manifest | version: "1.1.0"}})

      {:ok, versions} = Registry.list_versions("test")
      assert "1.0.0" in versions
      assert "1.1.0" in versions
    end

    test "lists all packages" do
      Registry.init()

      pkg1_data = %{
        manifest: %{name: "pkg1", version: "1.0.0", description: "", dependencies: %{}, policies: []},
        files: []
      }

      pkg2_data = %{
        manifest: %{name: "pkg2", version: "2.0.0", description: "", dependencies: %{}, policies: []},
        files: []
      }

      Registry.add("pkg1", "1.0.0", pkg1_data)
      Registry.add("pkg2", "2.0.0", pkg2_data)

      {:ok, packages} = Registry.list_packages()
      package_names = Enum.map(packages, fn {name, _latest, _versions} -> name end)

      assert "pkg1" in package_names
      assert "pkg2" in package_names
    end

    test "searches packages by name" do
      Registry.init()

      pkg_data = %{
        manifest: %{name: "acme-common", version: "1.0.0", description: "", dependencies: %{}, policies: []},
        files: []
      }

      Registry.add("acme-common", "1.0.0", pkg_data)
      Registry.add("acme-network", "1.0.0", %{pkg_data | manifest: %{pkg_data.manifest | name: "acme-network"}})

      {:ok, results} = Registry.search("acme")
      assert length(results) == 2

      {:ok, results} = Registry.search("network")
      assert length(results) == 1
    end

    test "fetches latest version" do
      Registry.init()

      pkg_data = %{
        manifest: %{name: "test", version: "1.0.0", description: "", dependencies: %{}, policies: []},
        files: []
      }

      Registry.add("test", "1.0.0", pkg_data)
      Registry.add("test", "1.2.0", %{pkg_data | manifest: %{pkg_data.manifest | version: "1.2.0"}})
      Registry.add("test", "1.1.0", %{pkg_data | manifest: %{pkg_data.manifest | version: "1.1.0"}})

      {:ok, fetched} = Registry.fetch("test", "latest")
      assert fetched.manifest.version == "1.2.0"
    end
  end

  describe "PackageManager" do
    test "initializes a new package" do
      {:ok, manifest} = PackageManager.init("my-package", version: "0.1.0")

      assert manifest.name == "my-package"
      assert manifest.version == "0.1.0"
      assert File.exists?("phronesis.ncl")
    end

    test "lists installed packages" do
      {:ok, packages} = PackageManager.list()
      assert packages == []

      # Create a fake installed package
      File.mkdir_p!(".phronesis/packages/test-pkg")

      manifest = %{
        name: "test-pkg",
        version: "1.0.0",
        description: "Test",
        dependencies: %{},
        policies: []
      }

      Manifest.write(manifest, ".phronesis/packages/test-pkg/phronesis.ncl")

      {:ok, packages} = PackageManager.list()
      assert length(packages) == 1
      assert {"test-pkg", "1.0.0", "Test"} in packages
    end

    test "formats package list" do
      packages = [
        {"pkg1", "1.0.0", "First package"},
        {"pkg2", "2.0.0", "Second package"}
      ]

      output = PackageManager.format_list(packages)

      assert output =~ "pkg1@1.0.0"
      assert output =~ "First package"
      assert output =~ "pkg2@2.0.0"
    end

    test "formats empty package list" do
      output = PackageManager.format_list([])
      assert output == "No packages installed"
    end
  end
end
