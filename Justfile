import? "contractile.just"

# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors
#
# Justfile for Phronesis - ethical reasoning language/runtime on BEAM
#
# Per AUTHORITY_STACK: All local operations must be invoked via `just <recipe>`

# Default recipe: list available commands
default:
    @just --list

# Run all tests
test:
    mix test

# Run the demo (produces decision traces)
demo:
    mix run -e 'Phronesis.Demo.run()'

# Run conformance test suite
conformance:
    mix run -e 'Phronesis.Demo.run_conformance()'

# Compile the project
build:
    mix compile

# Clean build artifacts
clean:
    mix clean

# Format code
format:
    mix format

# Check formatting without modifying
format-check:
    mix format --check-formatted

# Run the smoke test (golden path from ANCHOR)
smoke: test demo
    @echo "Smoke test passed: tests pass and demo produces traces"

# Start interactive REPL
repl:
    iex -S mix

# Parse a policy file (for debugging)
parse file:
    mix run -e 'IO.inspect(Phronesis.parse(File.read!("{{file}}")), limit: :infinity)'

# Run linter checks
lint:
    mix compile --warnings-as-errors

# Generate documentation
docs:
    mix docs

# Install dependencies
deps:
    mix deps.get

# Create compiled escript binary
escript:
    mix escript.build

# Run panic-attacker pre-commit scan
assail:
    @command -v panic-attack >/dev/null 2>&1 && panic-attack assail . || echo "panic-attack not found — install from https://github.com/hyperpolymath/panic-attacker"


# Print the current CRG grade (reads from READINESS.md '**Current Grade:** X' line)
crg-grade:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    echo "$$grade"

# Generate a shields.io badge markdown for the current CRG grade
# Looks for '**Current Grade:** X' in READINESS.md; falls back to X
crg-badge:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    case "$$grade" in \
      A) color="brightgreen" ;; B) color="green" ;; C) color="yellow" ;; \
      D) color="orange" ;; E) color="red" ;; F) color="critical" ;; \
      *) color="lightgrey" ;; esac; \
    echo "[![CRG $$grade](https://img.shields.io/badge/CRG-$$grade-$$color?style=flat-square)](https://github.com/hyperpolymath/standards/tree/main/component-readiness-grades)"
