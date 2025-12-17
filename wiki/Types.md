# Types

Phronesis is dynamically typed with a small set of value types.

---

## Type System Overview

### Dynamic Typing

Types are checked at runtime, not compile time:

```phronesis
CONST x = 10        # x is Integer
CONST y = "hello"   # y is String
CONST z = x + y     # Runtime error: cannot add Integer and String
```

### Type Coercion

Phronesis has minimal automatic type coercion:

- Integers are promoted to Floats in mixed arithmetic
- No implicit string conversion
- No truthy/falsy coercion (only Boolean is valid in conditions)

```phronesis
1 + 2.0         # 3.0 (Integer promoted to Float)
"x" + 1         # Error (no implicit conversion)
1 AND true      # Error (1 is not Boolean)
```

---

## Value Types

### Integer

Arbitrary precision integers.

```phronesis
# Literals
0
42
-17
1000000000000000000

# Operations
1 + 2           # 3
10 - 3          # 7
4 * 5           # 20
10 / 3          # 3 (integer division)
10 % 3          # 1 (modulo)

# Comparisons
1 < 2           # true
1 == 1          # true
```

### Float

IEEE 754 double-precision floating point.

```phronesis
# Literals
0.0
3.14159
-0.5
1.5e10          # Scientific notation (future)

# Operations
1.0 + 2.0       # 3.0
10.0 / 3.0      # 3.333...
1 + 2.0         # 3.0 (Integer promoted)

# Special values
# Infinity, -Infinity, NaN (from operations)
```

### String

Unicode text strings.

```phronesis
# Literals
""
"hello"
"hello world"
"line1\nline2"

# Operations (via Std.String, future)
# Std.String.length("hello")     # 5
# Std.String.concat("a", "b")    # "ab"
# Std.String.contains("hello", "ell")  # true

# Comparison
"a" == "a"      # true
"a" < "b"       # true (lexicographic)
```

### Boolean

Truth values for logical operations.

```phronesis
# Literals
true
false

# Operations
true AND false  # false
true OR false   # true
NOT true        # false

# From comparisons
1 < 2           # true
"a" == "b"      # false
```

### IPAddress

IPv4 and IPv6 addresses, with optional CIDR notation.

```phronesis
# IPv4 literals
192.0.2.1
10.0.0.0
0.0.0.0

# IPv4 CIDR literals
10.0.0.0/8
192.168.1.0/24
0.0.0.0/0

# IPv6 literals (future)
# 2001:db8::1
# ::1
# fe80::/10

# Operations (via Std.IP, future)
# Std.IP.in_subnet("10.0.0.1", "10.0.0.0/8")  # true
# Std.IP.is_private("192.168.1.1")            # true
```

### DateTime

ISO 8601 timestamps.

```phronesis
# Literals
2025-01-15T10:30:00Z
2025-12-31T23:59:59Z
2025-06-15T14:30:00+02:00

# Operations (via Std.Temporal)
Std.Temporal.now()                    # Current time
Std.Temporal.within_window("02:00", "04:00")  # Time check

# Comparison
dt1 < dt2       # Chronological order
```

### List

Ordered, heterogeneous collections.

```phronesis
# Literals
[]
[1, 2, 3]
["a", "b", "c"]
[1, "mixed", true, null]
[[1, 2], [3, 4]]

# Access (0-indexed, future)
# list[0]           # First element
# list[-1]          # Last element

# Operations
1 IN [1, 2, 3]      # true (membership)
# Std.List.length([1, 2, 3])    # 3 (future)
# Std.List.first([1, 2, 3])     # 1 (future)

# In conditions
route.prefix IN bogon_list      # Membership test
65001 IN route.as_path          # AS in path
```

### Record

Named field collections (similar to JSON objects).

```phronesis
# Literals
{}
{name: "test"}
{x: 1, y: 2}
{prefix: "10.0.0.0/8", origin_as: 65001, as_path: [65001, 65002]}

# Field access
route.prefix        # "10.0.0.0/24"
route.origin_as     # 65001
config.timeout      # 5000

# Nested access
response.data.items     # Nested field

# In conditions
route.prefix_length > 24
route.origin_as IN trusted_asns
```

### Null

Represents absence of a value.

```phronesis
# Literal
null

# Checking for null
x == null           # true if x is null

# From module calls
Std.Consensus.get_leader()  # null if no leader
```

---

## Type Checking

### Comparison Types

Comparing incompatible types returns `false`:

```phronesis
1 == "1"            # false (Integer vs String)
true == 1           # false (Boolean vs Integer)
[1] == {a: 1}       # false (List vs Record)
```

### Arithmetic Types

Arithmetic requires numeric types:

```phronesis
1 + 2               # OK: Integer + Integer
1.0 + 2.0           # OK: Float + Float
1 + 2.0             # OK: Integer promoted to Float
"1" + 2             # Error: String + Integer
```

### Logical Types

Logical operators require Boolean:

```phronesis
true AND false      # OK
1 AND 2             # Error: Integer not Boolean
"" OR true          # Error: String not Boolean
```

### IN Operator Types

Right operand must be List:

```phronesis
1 IN [1, 2, 3]      # OK: element IN List
1 IN 123            # Error: not a List
"a" IN "abc"        # Error: String not List (use Std.String.contains)
```

---

## Type Inference

Types are inferred from values:

```phronesis
# Inferred types
CONST a = 42                    # Integer
CONST b = 3.14                  # Float
CONST c = "hello"               # String
CONST d = true                  # Boolean
CONST e = [1, 2, 3]             # List of Integer
CONST f = {x: 1, y: 2}          # Record
CONST g = 192.0.2.1             # IPAddress
CONST h = 2025-01-15T10:30:00Z  # DateTime
```

---

## Type Conversions

Explicit conversions (via standard library, future):

```phronesis
# Integer <-> Float
# Std.Int.to_float(42)          # 42.0
# Std.Float.to_int(3.14)        # 3

# Integer <-> String
# Std.Int.parse("42")           # 42
# Std.Int.to_string(42)         # "42"

# Boolean <-> String
# Std.Bool.parse("true")        # true
# Std.Bool.to_string(true)      # "true"

# IP <-> String
# Std.IP.parse("10.0.0.1")      # IPAddress
# Std.IP.to_string(ip)          # "10.0.0.1"
```

---

## Special Type Behaviors

### List Equality

Lists are equal if same length and all elements equal:

```phronesis
[1, 2, 3] == [1, 2, 3]          # true
[1, 2, 3] == [1, 2]             # false
[1, 2, 3] == [3, 2, 1]          # false (order matters)
```

### Record Equality

Records are equal if same fields with equal values:

```phronesis
{a: 1, b: 2} == {a: 1, b: 2}    # true
{a: 1, b: 2} == {b: 2, a: 1}    # true (order doesn't matter)
{a: 1} == {a: 1, b: 2}          # false (different fields)
```

### IP Address Equality

IP addresses compared by value:

```phronesis
192.0.2.1 == 192.0.2.1          # true
10.0.0.0/8 == 10.0.0.0/8        # true
10.0.0.0/8 == 10.0.0.0/16       # false (different prefix length)
```

### DateTime Comparison

DateTimes compared chronologically:

```phronesis
2025-01-01T00:00:00Z < 2025-12-31T00:00:00Z  # true
```

---

## Future Type System Enhancements

### Optional Type Annotations (v0.3.x)

```phronesis
CONST max_len: Integer = 24
CONST name: String = "test"
CONST items: List<Integer> = [1, 2, 3]
```

### Union Types (v0.3.x)

```phronesis
type Result = Valid | Invalid | NotFound
```

### Refinement Types (v0.4.x)

```phronesis
type PrefixLength = Integer WHERE 0 <= _ <= 128
type ASN = Integer WHERE 0 <= _ <= 4294967295
```

---

## See Also

- [Language Overview](Language-Overview.md) - Core concepts
- [Syntax Reference](Syntax-Reference.md) - Complete syntax
- [Operators](Operators.md) - All operators
- [Advanced-Types](Advanced-Types.md) - Future type system
