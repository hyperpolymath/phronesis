# Std.RPKI

Resource Public Key Infrastructure (RPKI) validation module.

---

## Overview

The RPKI module provides functions for validating BGP route origins against the Resource Public Key Infrastructure (RPKI). It supports both real validators (Routinator, rpki-client) and a built-in mock database for testing.

---

## Import

```phronesis
IMPORT Std.RPKI
```

---

## Functions

### validate

Validate a route's origin AS against RPKI ROAs.

**Signature:**
```
Std.RPKI.validate(route) -> "valid" | "invalid" | "not_found"
```

**Parameters:**
- `route` - Record with `prefix` and `origin_as` fields

**Returns:**
- `"valid"` - A matching ROA authorizes this origin AS
- `"invalid"` - A ROA exists but doesn't authorize this origin AS
- `"not_found"` - No ROA covers this prefix

**Example:**
```phronesis
POLICY rpki_check:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI validation failed")
  PRIORITY: 200
```

**Validation Logic:**
1. Find all ROAs covering the announced prefix
2. Check if any ROA authorizes the origin AS
3. Verify prefix length is within ROA's max_length

```
Announced: 10.0.0.0/24 from AS 65001

ROA 1: 10.0.0.0/8, max_length=24, AS 65001
  - Prefix covered? Yes (10.0.0.0/24 within 10.0.0.0/8)
  - Length valid? Yes (24 <= 24)
  - AS matches? Yes (65001 == 65001)
  - Result: VALID

ROA 2: 10.0.0.0/8, max_length=16, AS 65001
  - Prefix covered? Yes
  - Length valid? No (24 > 16)
  - Result: Continue checking

If no ROA matches: NOT_FOUND or INVALID
```

---

### get_roas

Get all ROAs/VRPs covering a prefix.

**Signature:**
```
Std.RPKI.get_roas(prefix) -> List<ROA>
```

**Parameters:**
- `prefix` - IP prefix string (e.g., "10.0.0.0/24")

**Returns:**
List of ROA records:
```phronesis
[
  {prefix: "10.0.0.0/8", max_length: 24, asn: 65001},
  {prefix: "10.0.0.0/16", max_length: 24, asn: 65002}
]
```

**Example:**
```phronesis
POLICY check_roas:
  Std.RPKI.get_roas(route.prefix) == []
  THEN REPORT("No ROA coverage for prefix")
  PRIORITY: 50
```

---

### check_origin

Check if a route's origin AS is authorized.

**Signature:**
```
Std.RPKI.check_origin(route) -> Boolean
```

**Parameters:**
- `route` - Record with `prefix` and `origin_as` fields

**Returns:**
- `true` - Origin AS is authorized (validate returns "valid")
- `false` - Origin AS is not authorized

**Example:**
```phronesis
POLICY origin_check:
  NOT Std.RPKI.check_origin(route)
  THEN REJECT("Origin AS not authorized")
  PRIORITY: 200
```

---

## Configuration

### Validator Backend

Configure which RPKI validator to use:

```elixir
# config/config.exs
config :phronesis, Phronesis.Stdlib.StdRPKI,
  backend: :routinator,  # :routinator | :rpki_client | :mock
  host: "localhost",
  port: 8323,
  timeout: 5000
```

### Environment Variables

```bash
export PHRONESIS_RPKI_BACKEND=routinator
export PHRONESIS_RPKI_HOST=localhost
export PHRONESIS_RPKI_PORT=8323
```

### Supported Backends

| Backend | Description | Default Port |
|---------|-------------|--------------|
| `routinator` | NLnet Labs Routinator | 8323 |
| `rpki_client` | OpenBSD rpki-client | 8323 |
| `mock` | Built-in test data | N/A |

---

## Validation States

### Valid

A ROA exists that authorizes the origin AS for the announced prefix.

```
Prefix:    10.0.0.0/24
Origin AS: 65001
ROA:       10.0.0.0/8, max_length=24, AS=65001
Result:    VALID
```

### Invalid

A ROA exists covering the prefix, but it doesn't authorize the origin AS or the prefix is too specific.

```
# Wrong AS
Prefix:    10.0.0.0/24
Origin AS: 65002
ROA:       10.0.0.0/8, max_length=24, AS=65001
Result:    INVALID (wrong origin AS)

# Prefix too specific
Prefix:    10.0.0.0/28
Origin AS: 65001
ROA:       10.0.0.0/8, max_length=24, AS=65001
Result:    INVALID (28 > 24 max_length)
```

### Not Found

No ROA covers the announced prefix.

```
Prefix:    203.0.113.0/24
Origin AS: 65001
ROAs:      (none covering this prefix)
Result:    NOT_FOUND
```

---

## Common Patterns

### Strict RPKI (Reject Invalid and Not Found)

```phronesis
POLICY rpki_strict:
  Std.RPKI.validate(route) != "valid"
  THEN REJECT("RPKI not valid")
  PRIORITY: 200
```

### Permissive RPKI (Only Reject Invalid)

```phronesis
POLICY rpki_permissive:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI invalid")
  PRIORITY: 200

# Not-found routes are allowed to pass
```

### RPKI with Logging

```phronesis
POLICY rpki_with_logging:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI invalid")
  ELSE IF Std.RPKI.validate(route) == "not_found"
       THEN REPORT("Route has no RPKI coverage")
  PRIORITY: 200
```

### Conditional RPKI by Prefix Type

```phronesis
CONST critical_prefixes = ["1.1.1.0/24", "8.8.8.0/24"]

POLICY rpki_critical:
  route.prefix IN critical_prefixes
  AND Std.RPKI.validate(route) != "valid"
  THEN REJECT("Critical prefix requires RPKI valid")
  PRIORITY: 250

POLICY rpki_normal:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI invalid")
  PRIORITY: 200
```

---

## Testing

### Mock Mode

For testing, use the mock backend which includes sample ROAs:

```elixir
config :phronesis, Phronesis.Stdlib.StdRPKI,
  backend: :mock
```

Built-in mock ROAs:
```
1.0.0.0/24    max_length=24  AS 13335  (Cloudflare)
1.1.1.0/24    max_length=24  AS 13335  (Cloudflare)
8.8.8.0/24    max_length=24  AS 15169  (Google)
192.0.2.0/24  max_length=24  AS 64496  (Documentation)
```

### Test Examples

```elixir
defmodule RPKITest do
  use ExUnit.Case

  test "validates Cloudflare prefix" do
    route = %{prefix: "1.1.1.0/24", origin_as: 13335}
    assert Phronesis.Stdlib.StdRPKI.validate(route) == "valid"
  end

  test "rejects wrong origin" do
    route = %{prefix: "1.1.1.0/24", origin_as: 99999}
    assert Phronesis.Stdlib.StdRPKI.validate(route) == "invalid"
  end

  test "not found for uncovered prefix" do
    route = %{prefix: "203.0.113.0/24", origin_as: 65001}
    assert Phronesis.Stdlib.StdRPKI.validate(route) == "not_found"
  end
end
```

---

## Validator Setup

### Routinator

Install and run Routinator:

```bash
# Install
cargo install routinator

# Initialize (downloads trust anchors)
routinator init

# Run with RTR server
routinator server --rtr 127.0.0.1:3323 --http 127.0.0.1:8323
```

### rpki-client

Install and run rpki-client:

```bash
# On Debian/Ubuntu
apt install rpki-client

# Run
rpki-client -v
```

---

## Performance

### Caching

RPKI data is cached locally:
- Default cache TTL: 1 hour
- Refresh triggered on validator update
- Memory cache for hot paths

### Refresh

```elixir
# Force refresh
Phronesis.Stdlib.StdRPKI.refresh_cache()

# Get validator stats
Phronesis.Stdlib.StdRPKI.validator_stats()
# => %{vrps: 450000, last_update: ~U[2025-01-15 10:30:00Z]}
```

---

## See Also

- [RFC 6480](https://tools.ietf.org/html/rfc6480) - RPKI Architecture
- [RFC 6482](https://tools.ietf.org/html/rfc6482) - ROA Profile
- [RFC 8210](https://tools.ietf.org/html/rfc8210) - RTR Protocol
- [Std.BGP](Stdlib-BGP.md) - BGP operations
- [Tutorial: RPKI](Tutorial-RPKI.md) - RPKI validation tutorial
