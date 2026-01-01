# SPDX-License-Identifier: AGPL-3.0-or-later
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
