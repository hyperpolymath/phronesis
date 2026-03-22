# Language Overview

Phronesis is a minimal, declarative policy language designed for network configuration with formal safety guarantees.

---

## Design Philosophy

### Minimalism

Phronesis follows a strict complexity budget:

| Component | Budget | Actual |
|-----------|--------|--------|
| Grammar | ~40 lines EBNF | 38 lines |
| Keywords | ≤20 | 15 |
| Evaluation rules | ≤10 | 5 |
| Implementation | <2000 LOC | ~1800 LOC |

This minimalism serves two purposes:
1. **Security**: Smaller attack surface
2. **Verifiability**: Can be formally verified

### Safety Guarantees

Every Phronesis program provides:

1. **Termination**: All programs terminate (no infinite loops)
2. **Type Safety**: Operations are type-checked
3. **Sandbox Isolation**: No access to system resources
4. **Consensus Gating**: Critical actions require distributed agreement
5. **Non-repudiation**: All decisions are logged immutably

### Declarative Style

Phronesis is declarative, not imperative:

```phronesis
# Declarative: "What" not "How"
POLICY reject_bogons:
  route.prefix IN bogon_list
  THEN REJECT("Bogon prefix")
  PRIORITY: 100

# NOT imperative (this is NOT Phronesis):
# for each route in routes:
#   if route.prefix in bogon_list:
#     reject(route)
```

---

## Core Concepts

### Programs

A Phronesis program consists of declarations:

```phronesis
# Program = declarations
CONST max_length = 24           # Constant declaration
IMPORT Std.RPKI                 # Import declaration
POLICY my_policy: ...           # Policy declaration
```

### Constants

Constants bind names to values:

```phronesis
CONST name = value

# Examples
CONST max_prefix_len = 24
CONST trusted_asns = [13335, 15169, 32934]
CONST maintenance_start = "02:00"
CONST config = {threshold: 0.67, timeout: 5000}
```

Constants are:
- Immutable (cannot be reassigned)
- Evaluated once at load time
- Scoped to the entire program

### Imports

Import standard library modules:

```phronesis
IMPORT module_path [AS alias]

# Examples
IMPORT Std.RPKI
IMPORT Std.BGP AS bgp
IMPORT Std.Consensus
IMPORT Std.Temporal
```

### Policies

Policies are the core building block:

```phronesis
POLICY name:
  condition
  THEN action
  [ELSE action]
  PRIORITY: integer
```

Components:
- **name**: Unique identifier for the policy
- **condition**: Boolean expression that triggers the policy
- **THEN action**: Action when condition is true
- **ELSE action**: Optional action when condition is false
- **PRIORITY**: Determines evaluation order (higher = first)

Example:

```phronesis
POLICY rpki_validation:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI invalid")
  ELSE ACCEPT(route)
  PRIORITY: 200
```

### Priority Ordering

When multiple policies match, priority determines which executes:

```phronesis
# Evaluated first (highest priority)
POLICY critical_filter:
  is_critical(route)
  THEN REJECT("Critical filter")
  PRIORITY: 1000

# Evaluated second
POLICY rpki_check:
  NOT Std.RPKI.check_origin(route)
  THEN REJECT("RPKI invalid")
  PRIORITY: 200

# Evaluated last (lowest priority)
POLICY default:
  true
  THEN ACCEPT(route)
  PRIORITY: 1
```

---

## Expressions

### Literals

```phronesis
# Integers
42
-17
0

# Floats
3.14159
-0.5
1.0

# Strings
"hello world"
"route from AS 65001"
""

# Booleans
true
false

# IP Addresses
192.0.2.1
10.0.0.0/8
2001:db8::1

# DateTime (ISO 8601)
2025-01-15T10:30:00Z

# Lists
[]
[1, 2, 3]
["a", "b", "c"]
[1, "mixed", true]

# Records
{}
{prefix: "10.0.0.0/8"}
{name: "test", value: 42, active: true}
```

### Variables

Variables reference constants or context:

```phronesis
CONST x = 10
CONST name = "test"

# In conditions
x > 5              # References constant x
route.prefix       # References route context field
route.origin_as    # Nested field access
```

### Operators

#### Arithmetic
```phronesis
1 + 2      # Addition: 3
5 - 3      # Subtraction: 2
4 * 3      # Multiplication: 12
10 / 3     # Division: 3.333...
10 % 3     # Modulo: 1
```

#### Comparison
```phronesis
1 == 1     # Equal: true
1 != 2     # Not equal: true
1 < 2      # Less than: true
2 > 1      # Greater than: true
1 <= 1     # Less or equal: true
2 >= 2     # Greater or equal: true
```

#### Logical
```phronesis
true AND false    # Logical AND: false
true OR false     # Logical OR: true
NOT true          # Logical NOT: false
```

#### Membership
```phronesis
1 IN [1, 2, 3]              # true
"x" IN ["a", "b", "c"]      # false
"10.0.0.0/24" IN prefixes   # List membership
```

### Operator Precedence

From highest to lowest:

| Precedence | Operators | Associativity |
|------------|-----------|---------------|
| 1 | `NOT` | Right |
| 2 | `*`, `/`, `%` | Left |
| 3 | `+`, `-` | Left |
| 4 | `<`, `>`, `<=`, `>=` | Left |
| 5 | `==`, `!=`, `IN` | Left |
| 6 | `AND` | Left |
| 7 | `OR` | Left |

Use parentheses to override:

```phronesis
# Without parentheses
a OR b AND c        # Parsed as: a OR (b AND c)

# With parentheses
(a OR b) AND c      # Different meaning
```

### Module Calls

Call standard library functions:

```phronesis
module.function(arg1, arg2, ...)

# Examples
Std.RPKI.validate(route)
Std.BGP.extract_as_path(route)
Std.Consensus.require_votes(action, threshold: 0.67)
Std.Temporal.within_window("02:00", "04:00")
```

---

## Actions

Actions are the effects of policy execution.

### ACCEPT

Accept a route or value:

```phronesis
ACCEPT(route)
ACCEPT(route WITH {local_pref: 100})
ACCEPT("Approved")
```

### REJECT

Reject with a reason:

```phronesis
REJECT("RPKI validation failed")
REJECT("Bogon prefix not allowed")
```

### REPORT

Log to the consensus log:

```phronesis
REPORT("Unusual route detected from AS 65001")
REPORT({event: "route_accepted", prefix: route.prefix})
```

### EXECUTE

Execute a named function:

```phronesis
EXECUTE(send_alert, "admin@example.com", "Route hijack detected")
EXECUTE(update_metrics, {counter: "rejected_routes", value: 1})
```

### Conditional Actions

Actions can be conditional:

```phronesis
POLICY conditional_action:
  route.prefix_length > 24
  THEN IF route.origin_as IN trusted_asns
       THEN ACCEPT(route)
       ELSE REJECT("Untrusted origin for specific prefix")
  PRIORITY: 100
```

---

## Context Variables

Policies have access to context variables:

### Route Context

```phronesis
route.prefix           # "10.0.0.0/24"
route.prefix_length    # 24
route.origin_as        # 65001
route.as_path          # [65001, 65002, 65003]
route.next_hop         # "192.0.2.1"
route.local_pref       # 100
route.med              # 50
route.communities      # ["65001:100", "65001:200"]
route.afi              # "ipv4" or "ipv6"
```

### Environment Context

```phronesis
env.node_id            # Current node identifier
env.timestamp          # Current time
env.capabilities       # Granted capabilities
```

---

## Comments

Single-line comments start with `#`:

```phronesis
# This is a comment
CONST x = 10  # Inline comment

# Multi-line comments use multiple #
# Line 1
# Line 2
# Line 3
```

---

## Grammar Summary

```ebnf
program        = { declaration } ;
declaration    = policy_decl | const_decl | import_decl ;
policy_decl    = "POLICY" identifier ":" condition "THEN" action_block
                 [ "ELSE" action_block ] "PRIORITY:" integer ;
const_decl     = "CONST" identifier "=" expression ;
import_decl    = "IMPORT" module_path [ "AS" identifier ] ;
```

See [Grammar Reference](Reference-Grammar.md) for complete EBNF.

---

## Keywords

The 15 reserved keywords:

| Keyword | Purpose |
|---------|---------|
| `POLICY` | Declare a policy |
| `CONST` | Declare a constant |
| `IMPORT` | Import a module |
| `AS` | Alias for imports |
| `THEN` | Action clause |
| `ELSE` | Alternative action |
| `IF` | Conditional |
| `PRIORITY` | Policy priority |
| `AND` | Logical and |
| `OR` | Logical or |
| `NOT` | Logical not |
| `ACCEPT` | Accept action |
| `REJECT` | Reject action |
| `REPORT` | Report action |
| `EXECUTE` | Execute action |

---

## Type System

Phronesis is dynamically typed with these value types:

| Type | Description | Examples |
|------|-------------|----------|
| Integer | Arbitrary precision | `42`, `-17` |
| Float | IEEE 754 double | `3.14`, `-0.5` |
| String | Unicode text | `"hello"` |
| Boolean | Truth value | `true`, `false` |
| IPAddress | IPv4/IPv6 | `192.0.2.1` |
| DateTime | Timestamp | `2025-01-15T10:30:00Z` |
| List | Ordered collection | `[1, 2, 3]` |
| Record | Named fields | `{a: 1, b: 2}` |
| Null | Absence | `null` |

See [Types](Types.md) for details.

---

## Next Steps

- [Syntax Reference](Syntax-Reference.md) - Complete syntax
- [Types](Types.md) - Type system details
- [Standard Library](Stdlib-RPKI.md) - Built-in modules
- [Formal Semantics](Formal-Semantics.md) - Mathematical specification
