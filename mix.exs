# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.MixProject do
  use Mix.Project

  @version "0.1.0"
  @source_url "https://github.com/hyperpolymath/phronesis"

  def project do
    [
      app: :phronesis,
      version: @version,
      elixir: "~> 1.14",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      description: description(),
      package: package(),
      docs: docs(),
      dialyzer: dialyzer(),
      escript: escript()
    ]
  end

  def application do
    [
      extra_applications: [:logger, :crypto, :inets],
      mod: {Phronesis.Application, []}
    ]
  end

  defp deps do
    [
      # JSON encoding/decoding for LSP server
      {:jason, "~> 1.4"},

      # Raft consensus library for distributed consensus
      {:ra, "~> 3.1"},

      # Property-based testing with StreamData (CRG Grade C requirement)
      {:stream_data, "~> 1.0", only: :test}
    ]
    # Note: Additional dependencies can be added when hex.pm is available:
    # {:nimble_parsec, "~> 1.4"},
    # {:ex_doc, "~> 0.31", only: :dev, runtime: false},
    # {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
    # {:credo, "~> 1.7", only: [:dev, :test], runtime: false}
  end

  defp description do
    """
    Phronesis: A Policy Language for Network Configuration.

    A minimal, decidable DSL for expressing network policies with
    consensus-gated execution and formal verification guarantees.
    """
  end

  defp package do
    [
      name: "phronesis",
      licenses: ["PMPL-1.0-or-later"],
      links: %{"GitHub" => @source_url}
    ]
  end

  defp docs do
    [
      main: "Phronesis",
      source_url: @source_url,
      extras: ["README.adoc"]
    ]
  end

  defp dialyzer do
    [
      plt_add_apps: [:mix],
      plt_file: {:no_warn, "priv/plts/dialyzer.plt"}
    ]
  end

  defp escript do
    [
      main_module: Phronesis.CLI,
      name: "phronesis"
    ]
  end
end
