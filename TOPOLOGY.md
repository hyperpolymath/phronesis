<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# TOPOLOGY.md — phronesis

## Purpose

Phronesis is a provably safe language for agentic ethical reasoning, combining symbolic AI with neural adaptability. Built on Elixir/BEAM VM, it formalizes ethical reasoning in autonomous systems with formal logic, provable safety guarantees, and neuro-symbolic integration for value-aligned autonomous agents.

## Module Map

```
phronesis/
├── compiler/            # Core Phronesis compiler (OCaml/analysis)
├── academic/            # Academic papers and formal proofs
├── conformance/         # Conformance test suites and validation
├── bench/               # Performance benchmarking
├── _build/              # Build artifacts (OCaml dune)
└── .github/workflows/   # CI/CD (hypatia-scan, codeql, etc.)
```

## Data Flow

```
[Ethical Spec] ──► [Parser] ──► [Type Checker] ──► [Symbolic Reasoner] ──► [BEAM Bytecode]
                                       ↓                     ↓
                            [Formal Proofs]      [Provable Safety Properties]
```

## Key Components

- **Symbolic reasoning**: Formalize ethical constraints as first-class language features
- **Neural adaptability**: Integrate learned representations with symbolic logic
- **Provable safety**: All autonomous decisions backed by formal proofs
- **BEAM target**: Run on Erlang/Elixir production infrastructure
