# Quick Start

Get up and running with Phronesis in 5 minutes.

---

## Prerequisites

Ensure Phronesis is installed:

```bash
phronesis --version
# Phronesis 0.1.0
```

If not, see [Installation](Installation.md).

---

## Step 1: Create Your First Policy

Create a file called `my_first_policy.phr`:

```phronesis
# my_first_policy.phr
# A simple BGP policy that rejects private prefixes

CONST private_prefixes = ["10.0.0.0/8", "172.16.0.0/12", "192.168.0.0/16"]

POLICY reject_private:
  route.prefix IN private_prefixes
  THEN REJECT("Private prefix not allowed on public internet")
  PRIORITY: 100

POLICY accept_default:
  true
  THEN ACCEPT(route)
  PRIORITY: 1
```

---

## Step 2: Validate Syntax

Check your policy for syntax errors:

```bash
phronesis check my_first_policy.phr
```

Expected output:
```
✓ my_first_policy.phr: syntax OK
  2 policies defined
  1 constant defined
```

---

## Step 3: Parse and Inspect

View the parsed AST:

```bash
phronesis parse my_first_policy.phr
```

Output:
```
Program
├── Const: private_prefixes = ["10.0.0.0/8", "172.16.0.0/12", "192.168.0.0/16"]
├── Policy: reject_private (priority: 100)
│   ├── Condition: route.prefix IN private_prefixes
│   └── Action: REJECT("Private prefix not allowed on public internet")
└── Policy: accept_default (priority: 1)
    ├── Condition: true
    └── Action: ACCEPT(route)
```

---

## Step 4: Run the Policy

Execute the policy with a test route:

```bash
phronesis run my_first_policy.phr --route '{"prefix": "10.1.2.0/24", "origin_as": 65001}'
```

Output:
```
Policy: reject_private
Result: REJECT
Reason: Private prefix not allowed on public internet
```

Try a public prefix:

```bash
phronesis run my_first_policy.phr --route '{"prefix": "8.8.8.0/24", "origin_as": 15169}'
```

Output:
```
Policy: accept_default
Result: ACCEPT
```

---

## Step 5: Interactive REPL

Explore interactively:

```bash
phronesis repl
```

```
Phronesis v0.1.0 REPL
Type :help for commands, :quit to exit

phr> 1 + 2 * 3
7

phr> CONST x = 10
:ok

phr> x > 5 AND x < 20
true

phr> :load my_first_policy.phr
Loaded 2 policies, 1 constant

phr> :policies
1. reject_private (priority: 100)
2. accept_default (priority: 1)

phr> :eval route.prefix IN private_prefixes
   with route = {"prefix": "10.0.0.0/24"}
true

phr> :quit
Goodbye!
```

---

## Step 6: Add RPKI Validation

Enhance your policy with RPKI:

```phronesis
# secure_bgp.phr
IMPORT Std.RPKI
IMPORT Std.BGP

CONST private_prefixes = ["10.0.0.0/8", "172.16.0.0/12", "192.168.0.0/16"]
CONST max_as_path_length = 50

# Reject RPKI-invalid routes (highest priority)
POLICY rpki_invalid:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI validation failed - invalid origin AS")
  PRIORITY: 200

# Reject private/bogon prefixes
POLICY reject_private:
  route.prefix IN private_prefixes
  THEN REJECT("Private prefix not allowed")
  PRIORITY: 190

# Reject excessively long AS paths
POLICY as_path_limit:
  Std.BGP.as_path_length(route) > max_as_path_length
  THEN REJECT("AS path too long")
  PRIORITY: 180

# Accept everything else
POLICY accept_default:
  true
  THEN ACCEPT(route)
  PRIORITY: 1
```

Run with RPKI validation:

```bash
phronesis run secure_bgp.phr --route '{"prefix": "1.1.1.0/24", "origin_as": 13335}'
```

---

## Step 7: Project Structure

For larger projects, organize your policies:

```
my_network_policies/
├── phronesis.toml          # Project configuration
├── policies/
│   ├── bgp/
│   │   ├── security.phr    # Security policies
│   │   ├── peering.phr     # Peering policies
│   │   └── customer.phr    # Customer policies
│   └── internal/
│       └── routing.phr     # Internal routing
├── tests/
│   ├── security_test.exs   # Policy tests
│   └── fixtures/
│       └── routes.json     # Test data
└── docs/
    └── policy_guide.md     # Documentation
```

Initialize a project:

```bash
mkdir my_network_policies
cd my_network_policies
phronesis init
```

---

## Common Patterns

### Pattern 1: Conditional Actions

```phronesis
POLICY conditional_accept:
  route.prefix_length <= 24
  THEN IF route.origin_as == 65001
       THEN ACCEPT(route)
       ELSE REPORT("Unknown origin for prefix")
  PRIORITY: 100
```

### Pattern 2: Using Constants

```phronesis
CONST trusted_asns = [13335, 15169, 32934]
CONST max_prefix_len_v4 = 24
CONST max_prefix_len_v6 = 48

POLICY trusted_networks:
  route.origin_as IN trusted_asns
  AND route.prefix_length <= max_prefix_len_v4
  THEN ACCEPT(route)
  PRIORITY: 150
```

### Pattern 3: Combining Conditions

```phronesis
POLICY complex_filter:
  (route.prefix_length >= 8 AND route.prefix_length <= 24)
  AND NOT (route.prefix IN bogon_list)
  AND (Std.RPKI.validate(route) == "valid" OR Std.RPKI.validate(route) == "not_found")
  THEN ACCEPT(route)
  PRIORITY: 100
```

---

## Next Steps

Now that you have the basics:

1. **[Language Overview](Language-Overview.md)** - Understand the full language
2. **[Standard Library](Stdlib-RPKI.md)** - Explore Std.RPKI, Std.BGP, etc.
3. **[CLI Reference](CLI-Reference.md)** - Master the command line
4. **[Tutorial: BGP Security](Tutorial-BGP-Security.md)** - Complete BGP security setup
5. **[Testing](Testing.md)** - Write tests for your policies

---

## Getting Help

- Run `phronesis --help` for CLI help
- Run `phronesis repl` then `:help` for REPL commands
- See [FAQ](FAQ.md) for common questions
- Open an issue on [GitHub](https://github.com/hyperpolymath/phronesis/issues)
