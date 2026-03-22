# Frequently Asked Questions

Common questions about Phronesis.

---

## General

### What is Phronesis?

Phronesis is a minimal domain-specific language for expressing network policies with formal safety guarantees. It provides:

- Consensus-gated execution
- Formal decidability (always terminates)
- Type safety
- Audit logging

### Why the name "Phronesis"?

Phronesis (φρόνησις) is an ancient Greek word meaning "practical wisdom" - the ability to discern the appropriate course of action in specific circumstances. This reflects the language's purpose: making wise routing decisions based on policy.

### What makes Phronesis different from other policy languages?

1. **Formal guarantees**: Every program terminates, no infinite loops possible
2. **Consensus-gated**: Critical actions require distributed agreement
3. **Minimal**: ~40 lines of grammar, 15 keywords, 5 evaluation rules
4. **Verifiable**: Small enough to formally verify

### Is Phronesis production-ready?

Phronesis v0.1.x is suitable for evaluation and testing. Production use is recommended starting with v1.0.0 (planned Q2 2026). See the [Roadmap](../ROADMAP.md).

---

## Language

### Why can't I define functions?

Phronesis deliberately excludes user-defined functions to:
1. Guarantee termination (no recursion)
2. Simplify formal verification
3. Keep the complexity budget

Instead, use:
- Constants for reusable values
- Module imports for reusable logic
- Multiple policies for complex flows

### Why is there no loop construct?

Loops can lead to non-termination. Phronesis guarantees all programs terminate. For iterating over collections, use:

```phronesis
# List membership
route.prefix IN bogon_list

# Module functions handle iteration internally
Std.BGP.as_path_length(route) > 50
```

### How do I handle errors?

Phronesis uses result values instead of exceptions:

```phronesis
# Check for valid result
Std.RPKI.validate(route) == "invalid"
THEN REJECT("RPKI invalid")

# Handle "not found" case
Std.RPKI.validate(route) == "not_found"
THEN REPORT("No RPKI coverage")
```

### Can I extend the language?

The core language is fixed, but you can:
1. Create custom modules in Elixir
2. Use the module system for extensions
3. Propose RFCs for language changes

---

## Installation

### Which Elixir version do I need?

Elixir 1.14 or later with Erlang/OTP 25+.

### Does it work on Windows?

Yes, via WSL2. Native Windows support is planned.

### How do I update Phronesis?

```bash
# From binary
curl -LO https://github.com/hyperpolymath/phronesis/releases/latest/download/phronesis-linux-amd64.tar.gz
tar xzf phronesis-linux-amd64.tar.gz
sudo mv phronesis /usr/local/bin/

# From source
cd phronesis
git pull
mix deps.get
mix escript.build
```

---

## RPKI

### Do I need an RPKI validator?

For testing, Phronesis includes mock RPKI data. For production, you need a validator like Routinator or rpki-client.

### How do I configure RPKI validation?

```bash
# Environment variables
export PHRONESIS_RPKI_BACKEND=routinator
export PHRONESIS_RPKI_HOST=localhost
export PHRONESIS_RPKI_PORT=8323
```

Or in config:

```elixir
config :phronesis, Phronesis.Stdlib.StdRPKI,
  backend: :routinator,
  host: "localhost",
  port: 8323
```

### What's the difference between "invalid" and "not_found"?

- **invalid**: A ROA exists that contradicts the announcement (wrong origin AS)
- **not_found**: No ROA covers the prefix (origin cannot be verified)

---

## Consensus

### How does consensus work?

Phronesis uses Raft consensus:
1. A leader is elected among nodes
2. Actions are proposed to the leader
3. Leader replicates to followers
4. Once majority acknowledges, action commits
5. All nodes apply the committed action

### What happens if consensus fails?

The action is not executed. You can handle this:

```phronesis
POLICY with_fallback:
  Std.Consensus.get_leader() != null
  THEN IF Std.Consensus.require_votes(ACCEPT(route))
       THEN ACCEPT(route)
       ELSE REJECT("Consensus denied")
  ELSE REPORT("No consensus leader available")
  PRIORITY: 100
```

### How many nodes do I need?

- 3 nodes: Tolerates 1 failure
- 5 nodes: Tolerates 2 failures
- 7 nodes: Tolerates 3 failures

Formula: To tolerate f failures, you need 2f+1 nodes.

---

## Performance

### How fast is policy evaluation?

Current benchmarks (v0.1.x):
- Parse: ~1,000 policies/second
- Execute: ~10,000 decisions/second
- Consensus: ~100 commits/second

Target for v1.0:
- Parse: 1M policies/second
- Execute: 2M decisions/second
- Consensus: 100K commits/second

### How can I improve performance?

1. Use simpler conditions (fewer ANDs/ORs)
2. Order policies by likelihood (most common matches first)
3. Use RPKI caching
4. Tune consensus settings

---

## Debugging

### How do I debug a policy?

Use the REPL:

```bash
phronesis repl --load my_policy.phr

phr> :policies
1. rpki_check (priority: 200)
2. default (priority: 1)

phr> :eval Std.RPKI.validate(route)
   with route = {"prefix": "1.1.1.0/24", "origin_as": 13335}
"valid"
```

### Why isn't my policy matching?

Check:
1. Priority order (higher = evaluated first)
2. Condition evaluation (use `:eval` in REPL)
3. Variable bindings (use `:state` in REPL)

```bash
phr> :eval route.prefix IN bogon_list
   with route = {"prefix": "10.0.0.0/24"}
true
```

### How do I trace execution?

Enable verbose mode:

```bash
phronesis run policy.phr --route '...' --verbose
```

Output:
```
[DEBUG] Evaluating policy: rpki_check (priority: 200)
[DEBUG] Condition: Std.RPKI.validate(route) == "invalid"
[DEBUG] Std.RPKI.validate called with %{prefix: "..."}
[DEBUG] Result: "not_found"
[DEBUG] Condition evaluated to: false
[DEBUG] Evaluating policy: default (priority: 1)
...
```

---

## Integration

### Can I use Phronesis with my router?

Integration with routers is planned for v0.3.x. Currently:
- Cisco IOS-XR: Planned
- Juniper Junos: Planned
- Arista EOS: Planned

For now, Phronesis can generate configuration that you apply manually.

### How do I integrate with monitoring?

Phronesis can export metrics to Prometheus (planned v0.4.x). Currently, use REPORT actions:

```phronesis
POLICY log_all:
  true
  THEN REPORT({
    event: "route_decision",
    prefix: route.prefix,
    result: "accept"
  })
  PRIORITY: 1
```

---

## Contributing

### How do I report a bug?

Open an issue at https://github.com/hyperpolymath/phronesis/issues with:
- Description of the problem
- Steps to reproduce
- Expected vs actual behavior
- Phronesis version

### How do I request a feature?

Start a discussion at https://github.com/hyperpolymath/phronesis/discussions. For significant features, we use an RFC process.

### Can I contribute code?

Yes! See [Contributing](Contributing.md) for guidelines.

---

## See Also

- [Quick-Start](Quick-Start.md) - Getting started
- [Language-Overview](Language-Overview.md) - Language concepts
- [CLI-Reference](CLI-Reference.md) - Command reference
- [Troubleshooting](#) - Common issues
