# CLI Reference

Command-line interface for Phronesis.

---

## Synopsis

```bash
phronesis [OPTIONS] COMMAND [ARGS]
```

---

## Global Options

| Option | Description |
|--------|-------------|
| `--version`, `-v` | Show version information |
| `--help`, `-h` | Show help message |
| `--verbose` | Enable verbose output |
| `--quiet`, `-q` | Suppress non-error output |
| `--config FILE` | Use specified config file |

---

## Commands

### run

Execute a policy file against a route.

```bash
phronesis run FILE [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--route JSON` | Route data as JSON string |
| `--route-file FILE` | Read route from file |
| `--context JSON` | Additional context variables |
| `--output FORMAT` | Output format: text, json, table |

**Examples:**

```bash
# Run with inline route
phronesis run policy.phr --route '{"prefix": "10.0.0.0/24", "origin_as": 65001}'

# Run with route from file
phronesis run policy.phr --route-file route.json

# JSON output
phronesis run policy.phr --route '...' --output json

# With context
phronesis run policy.phr --route '...' --context '{"local_as": 65000}'
```

**Output:**

```
Policy: rpki_validation
Result: REJECT
Reason: RPKI validation failed

Execution time: 2.3ms
Policies evaluated: 3
```

---

### parse

Parse a policy file and display the AST.

```bash
phronesis parse FILE [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--format FORMAT` | Output format: tree, json, sexpr |
| `--tokens` | Show tokens instead of AST |

**Examples:**

```bash
# Show AST tree
phronesis parse policy.phr

# Show as JSON
phronesis parse policy.phr --format json

# Show tokens
phronesis parse policy.phr --tokens
```

**Output (tree):**

```
Program
├── Const: max_len = 24
├── Import: Std.RPKI
└── Policy: rpki_check (priority: 200)
    ├── Condition
    │   └── BinaryOp: ==
    │       ├── Call: Std.RPKI.validate(route)
    │       └── String: "invalid"
    └── Action: REJECT("RPKI validation failed")
```

---

### check

Validate syntax and semantics of a policy file.

```bash
phronesis check FILE [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--strict` | Enable strict checking |
| `--warnings` | Show warnings |
| `--self-test` | Run internal self-test |

**Examples:**

```bash
# Basic check
phronesis check policy.phr

# Strict mode
phronesis check policy.phr --strict

# Check multiple files
phronesis check policies/*.phr
```

**Output (success):**

```
✓ policy.phr: syntax OK
  3 policies defined
  2 constants defined
  1 import
```

**Output (error):**

```
✗ policy.phr: syntax error

  Error at line 5, column 12:
    POLICY test: x = 5
                   ^
  Expected 'THEN' after condition, found '='
```

---

### repl

Start an interactive REPL session.

```bash
phronesis repl [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--load FILE` | Load file on startup |
| `--no-color` | Disable color output |
| `--history FILE` | History file location |

**Examples:**

```bash
# Start REPL
phronesis repl

# Load file on startup
phronesis repl --load policy.phr
```

**REPL Session:**

```
Phronesis v0.1.0 REPL
Type :help for commands, :quit to exit

phr> 1 + 2
3

phr> CONST x = 10
:ok

phr> x * 2
20

phr> :load policy.phr
Loaded 3 policies, 2 constants

phr> :policies
1. rpki_check (priority: 200)
2. bogon_filter (priority: 190)
3. default_accept (priority: 1)

phr> :quit
Goodbye!
```

**REPL Commands:**

| Command | Description |
|---------|-------------|
| `:help` | Show help |
| `:quit`, `:q` | Exit REPL |
| `:load FILE` | Load policy file |
| `:reload` | Reload current file |
| `:clear` | Clear state |
| `:state` | Show current state |
| `:policies` | List loaded policies |
| `:type EXPR` | Show expression type |
| `:ast EXPR` | Show expression AST |

---

### fmt (Planned v0.2.x)

Format policy files.

```bash
phronesis fmt FILE [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--check` | Check if formatted (exit 1 if not) |
| `--write`, `-w` | Write changes to file |
| `--diff` | Show diff |

**Examples:**

```bash
# Check formatting
phronesis fmt policy.phr --check

# Format in place
phronesis fmt policy.phr --write

# Show diff
phronesis fmt policy.phr --diff
```

---

### lint (Planned v0.2.x)

Run static analysis on policy files.

```bash
phronesis lint FILE [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--fix` | Auto-fix issues where possible |
| `--rules FILE` | Custom rules file |
| `--severity LEVEL` | Minimum severity: error, warning, info |

**Examples:**

```bash
# Run linter
phronesis lint policy.phr

# With auto-fix
phronesis lint policy.phr --fix
```

**Output:**

```
policy.phr:12:5 warning: Unused constant 'old_value'
policy.phr:15:1 error: Unreachable policy (lower priority than catch-all)
policy.phr:20:10 info: Consider using Std.RPKI.check_origin() instead

Found 1 error, 1 warning, 1 info
```

---

### test (Planned v0.2.x)

Run policy tests.

```bash
phronesis test [FILE|DIR] [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--filter PATTERN` | Run tests matching pattern |
| `--coverage` | Generate coverage report |
| `--timeout MS` | Test timeout |
| `--parallel` | Run tests in parallel |

**Examples:**

```bash
# Run all tests
phronesis test

# Run specific test file
phronesis test test/rpki_test.exs

# With coverage
phronesis test --coverage
```

---

### doc (Planned v0.2.x)

Generate documentation from policy files.

```bash
phronesis doc [DIR] [OPTIONS]
```

**Options:**

| Option | Description |
|--------|-------------|
| `--output DIR` | Output directory |
| `--format FORMAT` | Format: html, markdown |

**Examples:**

```bash
# Generate docs
phronesis doc policies/ --output docs/

# Markdown format
phronesis doc policies/ --format markdown
```

---

## Configuration

### Config File

Create `phronesis.toml` in your project root:

```toml
[project]
name = "my-policies"
version = "1.0.0"

[phronesis]
strict = true
warnings = true

[rpki]
backend = "routinator"
host = "localhost"
port = 8323

[consensus]
threshold = 0.67
timeout = 5000
```

### Environment Variables

| Variable | Description |
|----------|-------------|
| `PHRONESIS_CONFIG` | Config file path |
| `PHRONESIS_RPKI_BACKEND` | RPKI backend |
| `PHRONESIS_RPKI_HOST` | RPKI validator host |
| `PHRONESIS_RPKI_PORT` | RPKI validator port |
| `PHRONESIS_NODE_ID` | Consensus node ID |
| `PHRONESIS_PEERS` | Consensus peer list |

---

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | General error |
| 2 | Syntax error |
| 3 | Runtime error |
| 4 | File not found |
| 5 | Consensus failure |

---

## Examples

### Basic Workflow

```bash
# 1. Create policy file
cat > my_policy.phr << 'EOF'
IMPORT Std.RPKI

POLICY rpki_check:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI invalid")
  PRIORITY: 200

POLICY default:
  true
  THEN ACCEPT(route)
  PRIORITY: 1
EOF

# 2. Validate syntax
phronesis check my_policy.phr

# 3. Test with sample route
phronesis run my_policy.phr \
  --route '{"prefix": "10.0.0.0/24", "origin_as": 65001}'

# 4. Start REPL for exploration
phronesis repl --load my_policy.phr
```

### CI/CD Integration

```bash
#!/bin/bash
# ci-check.sh

set -e

echo "Checking syntax..."
phronesis check policies/*.phr --strict

echo "Running tests..."
phronesis test test/

echo "Checking formatting..."
phronesis fmt policies/*.phr --check

echo "All checks passed!"
```

### Batch Processing

```bash
# Process multiple routes
cat routes.jsonl | while read route; do
  phronesis run policy.phr --route "$route" --output json
done

# With jq for filtering
cat routes.jsonl | while read route; do
  result=$(phronesis run policy.phr --route "$route" --output json)
  echo "$result" | jq -c 'select(.result == "REJECT")'
done
```

---

## See Also

- [REPL-Guide](REPL-Guide.md) - Interactive REPL details
- [Testing](Testing.md) - Test framework
- [Quick-Start](Quick-Start.md) - Getting started
