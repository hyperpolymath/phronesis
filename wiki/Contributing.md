# Contributing to Phronesis

Thank you for your interest in contributing to Phronesis! This guide explains how to get involved.

---

## Code of Conduct

By participating in this project, you agree to abide by our [Code of Conduct](Code-of-Conduct.md).

---

## Ways to Contribute

### 1. Report Bugs

Found a bug? [Open an issue](https://github.com/hyperpolymath/phronesis/issues/new?template=bug_report.md) with:

- Clear description of the problem
- Steps to reproduce
- Expected vs actual behavior
- Phronesis version
- Operating system

### 2. Suggest Features

Have an idea? [Open a discussion](https://github.com/hyperpolymath/phronesis/discussions/new) to:

- Describe the use case
- Explain the proposed solution
- Discuss alternatives

### 3. Improve Documentation

Documentation improvements are always welcome:

- Fix typos and clarify wording
- Add examples
- Write tutorials
- Translate documentation

### 4. Write Code

Code contributions include:

- Bug fixes
- New features
- Performance improvements
- Test coverage
- Tooling improvements

---

## Development Setup

### Prerequisites

- Erlang/OTP 25+
- Elixir 1.14+
- Git

### Clone and Build

```bash
# Fork the repository on GitHub first, then:
git clone https://github.com/YOUR_USERNAME/phronesis.git
cd phronesis

# Add upstream remote
git remote add upstream https://github.com/hyperpolymath/phronesis.git

# Install dependencies
mix deps.get

# Run tests
mix test

# Build CLI
mix escript.build
```

### Development Workflow

```bash
# Create feature branch
git checkout -b feature/my-feature

# Make changes and test
mix test

# Check formatting
mix format --check-formatted

# Run linter (when available)
mix credo

# Commit changes
git commit -m "Add feature X"

# Push to your fork
git push origin feature/my-feature
```

---

## Pull Request Process

### 1. Before You Start

- Check existing issues and PRs
- For significant changes, open a discussion first
- Review the [Roadmap](../ROADMAP.md)

### 2. Create PR

- Branch from `main`
- Follow [commit message conventions](#commit-messages)
- Include tests for new functionality
- Update documentation as needed

### 3. PR Template

```markdown
## Summary
Brief description of changes.

## Related Issues
Fixes #123

## Changes
- Added X
- Modified Y
- Removed Z

## Testing
- [ ] Added unit tests
- [ ] All tests pass
- [ ] Tested manually

## Documentation
- [ ] Updated relevant docs
- [ ] Added examples
```

### 4. Review Process

1. CI must pass
2. At least one maintainer approval
3. No unresolved conversations
4. Up-to-date with main branch

---

## Commit Messages

Follow [Conventional Commits](https://www.conventionalcommits.org/):

```
type(scope): description

[optional body]

[optional footer]
```

### Types

| Type | Description |
|------|-------------|
| `feat` | New feature |
| `fix` | Bug fix |
| `docs` | Documentation |
| `style` | Formatting |
| `refactor` | Code restructuring |
| `test` | Adding tests |
| `chore` | Maintenance |
| `perf` | Performance |

### Examples

```
feat(lexer): add IPv6 address literal support

fix(parser): handle empty list in expressions
Fixes #42

docs(wiki): add RPKI tutorial

test(interpreter): add property-based tests for evaluation

chore(deps): update dependencies
```

---

## Code Style

### Elixir Style

Follow the [Elixir Style Guide](https://github.com/christopheradams/elixir_style_guide):

```elixir
# Good
defmodule Phronesis.Lexer do
  @moduledoc """
  Tokenizes Phronesis source code.
  """

  @doc """
  Tokenizes input string into a list of tokens.
  """
  @spec tokenize(String.t()) :: {:ok, [Token.t()]} | {:error, term()}
  def tokenize(input) when is_binary(input) do
    # Implementation
  end
end

# Use pattern matching
def process({:ok, result}), do: handle_success(result)
def process({:error, reason}), do: handle_error(reason)

# Prefer pipeline operator
input
|> String.trim()
|> String.split("\n")
|> Enum.map(&process_line/1)
```

### Documentation Style

```elixir
@moduledoc """
Module summary (one line).

Detailed description of the module's purpose and usage.

## Examples

    iex> Phronesis.Lexer.tokenize("POLICY x: true THEN ACCEPT() PRIORITY: 1")
    {:ok, [%Token{type: :policy}, ...]}

## See Also

- `Phronesis.Parser`
- `Phronesis.Interpreter`
"""

@doc """
Function summary (one line).

## Parameters

- `input` - The source code string to tokenize

## Returns

- `{:ok, tokens}` - List of tokens on success
- `{:error, reason}` - Error tuple on failure

## Examples

    tokenize("CONST x = 42")
    {:ok, [%Token{type: :const}, ...]}
"""
```

---

## Testing Guidelines

### Test Structure

```elixir
defmodule Phronesis.LexerTest do
  use ExUnit.Case, async: true

  describe "tokenize/1" do
    test "tokenizes keywords" do
      assert {:ok, tokens} = Phronesis.Lexer.tokenize("POLICY")
      assert [%{type: :policy}] = tokens
    end

    test "handles empty input" do
      assert {:ok, []} = Phronesis.Lexer.tokenize("")
    end

    test "returns error for invalid input" do
      assert {:error, _} = Phronesis.Lexer.tokenize("@@@")
    end
  end
end
```

### Test Coverage

- Aim for 90%+ coverage
- Test edge cases
- Include property-based tests for core functionality

---

## RFC Process

For significant changes, we use an RFC (Request for Comments) process:

### 1. Create RFC

```markdown
# RFC: Feature Name

## Summary
One paragraph explanation.

## Motivation
Why are we doing this?

## Design
Detailed design explanation.

## Alternatives
What other designs were considered?

## Drawbacks
What are the downsides?

## Open Questions
What needs to be resolved?
```

### 2. Discussion

- Open PR with RFC in `rfcs/` directory
- Community discussion
- Revisions based on feedback

### 3. Decision

- Maintainer review
- Accept, reject, or request changes
- If accepted, move to implementation

---

## Issue Labels

| Label | Description |
|-------|-------------|
| `bug` | Something isn't working |
| `enhancement` | New feature request |
| `documentation` | Documentation improvement |
| `good first issue` | Good for newcomers |
| `help wanted` | Extra attention needed |
| `question` | Further information requested |
| `wontfix` | Will not be worked on |

---

## Getting Help

- **Discord**: [Community chat](#)
- **Discussions**: [GitHub Discussions](https://github.com/hyperpolymath/phronesis/discussions)
- **Issues**: [GitHub Issues](https://github.com/hyperpolymath/phronesis/issues)

---

## Recognition

Contributors are recognized in:

- [CONTRIBUTORS.md](../CONTRIBUTORS.md)
- Release notes
- Project website

---

## License

By contributing, you agree that your contributions will be licensed under the [AGPL-3.0](../LICENSE) license.
