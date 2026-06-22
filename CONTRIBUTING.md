<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Contributing to Phronesis

Thanks for your interest in contributing! Phronesis is a neuro-symbolic policy
language for provably-safe agentic ethical reasoning, with an Elixir/BEAM
reference implementation and a Rust → WASM production compiler.

## Getting Started

```bash
# Clone the repository
git clone https://github.com/hyperpolymath/phronesis.git
cd phronesis

# Install dependencies (BEAM toolchain + just)
mix deps.get

# Verify setup
just build   # mix compile
just test    # run the test suite
```

### Repository Structure
```
phronesis/
├── lib/phronesis/        # Reference implementation (Elixir/BEAM):
│                         #   lexer, parser, type checker, interpreter,
│                         #   consensus, LSP, debugger, profiler, reflexion
├── compiler/             # Rust → WASM compiler (phronesis-ast, phronesis-wasm)
├── spec/                 # Grammar (EBNF) + formal semantics
├── formal/               # TLA+ consensus specification
├── academic/             # Formal proofs (Lean4 / Agda / Coq)
├── conformance/          # Conformance test suites
├── bench/                # Benchmarks
├── docs/                 # AsciiDoc design docs (incl. REFLEXION.adoc)
├── examples/             # Example .phr policies
├── test/                 # ExUnit test suite
├── editors/              # VSCode extension + grammars
├── .machine_readable/    # A2ML metadata (6a2/) + contractiles
├── .github/workflows/    # CI/CD
├── CHANGELOG.md  CODE_OF_CONDUCT.md  CONTRIBUTING.md  SECURITY.md
├── GOVERNANCE.adoc  MAINTAINERS.adoc  README.adoc  EXPLAINME.adoc
├── LICENSE  LICENSES/    # MPL-2.0 (code) + CC-BY-SA-4.0 (docs)
├── mix.exs  Justfile  Mustfile
└── guix.scm
```

---

## How to Contribute

### Reporting Bugs

**Before reporting**:
1. Search existing issues
2. Check if it's already fixed in `main`
3. Determine which perimeter the bug affects

**When reporting**:

Use the [bug report template](.github/ISSUE_TEMPLATE/bug_report.md) and include:

- Clear, descriptive title
- Environment details (OS, versions, toolchain)
- Steps to reproduce
- Expected vs actual behaviour
- Logs, screenshots, or minimal reproduction

### Suggesting Features

**Before suggesting**:
1. Check the [roadmap](ROADMAP.md) if available
2. Search existing issues and discussions
3. Consider which perimeter the feature belongs to

**When suggesting**:

Use the [feature request template](.github/ISSUE_TEMPLATE/feature_request.md) and include:

- Problem statement (what pain point does this solve?)
- Proposed solution
- Alternatives considered
- Which perimeter this affects

### Your First Contribution

Look for issues labelled:

- [`good first issue`](https://github.com/hyperpolymath/phronesis/labels/good%20first%20issue) — Simple Perimeter 3 tasks
- [`help wanted`](https://github.com/hyperpolymath/phronesis/labels/help%20wanted) — Community help needed
- [`documentation`](https://github.com/hyperpolymath/phronesis/labels/documentation) — Docs improvements
- [`perimeter-3`](https://github.com/hyperpolymath/phronesis/labels/perimeter-3) — Community sandbox scope

---

## Development Workflow

### Branch Naming
```
docs/short-description       # Documentation (P3)
test/what-added              # Test additions (P3)
feat/short-description       # New features (P2)
fix/issue-number-description # Bug fixes (P2)
refactor/what-changed        # Code improvements (P2)
security/what-fixed          # Security fixes (P1-2)
```

### Commit Messages

We follow [Conventional Commits](https://www.conventionalcommits.org/):
```
<type>(<scope>): <description>

[optional body]

[optional footer]
