<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Architecture

Phronesis is a provably safer language for agentic ethical reasoning. The
repository is a multi-layer project: an Elixir reference implementation, a Rust
compiler workspace, and a formal-verification layer that gates the metatheory
in CI.

## Layout

```
.
├── lib/, src/, mix.exs        # Elixir reference implementation (core language)
├── compiler/
│   ├── phronesis-ast/         # Rust AST crate
│   └── phronesis-wasm/        # Rust → WASM compiler target
├── formal/                    # TLA+ BFT consensus spec (PhronesisConsensus.tla)
│                              #   gated by .github/workflows/tla-consensus.yml
├── academic/formal-verification/lean4/
│                              # Lean 4 metatheory, gated by lean.yml (lake build)
├── conformance/               # Conformance suite, gated by conformance.yml
├── spec/, docs/, wiki/        # Language specification and documentation
├── editors/, syntax/          # Editor support (TextMate, Vim, Emacs)
├── schemas/, configs/         # Machine-readable schemas and configuration
├── LICENSES/                  # Full licence texts (MPL-2.0 + CC-BY-SA-4.0)
└── .machine_readable/         # A2ML manifests and estate policy files
```

## Verification gates

- **Lean 4** (`lean.yml`): builds the metatheory with `lake build`.
- **TLA+** (`tla-consensus.yml`): model-checks the BFT consensus spec with TLC.
- **Conformance** (`conformance.yml`): runs the language conformance suite.

## Licensing

Code is MPL-2.0; documentation is CC-BY-SA-4.0 (dual SPDX headers — see
`LICENSING.adoc`). AGPL is deliberately not used in this repository.

For governance and maintainers see `GOVERNANCE.adoc` and `MAINTAINERS.adoc`.
