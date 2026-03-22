# Tutorial: BGP Security Policy

Learn to create comprehensive BGP security policies with Phronesis.

---

## Overview

This tutorial walks through building a production-grade BGP security policy that:

1. Validates routes using RPKI
2. Filters bogon prefixes
3. Enforces prefix length limits
4. Checks AS path sanity
5. Applies community-based routing

---

## Prerequisites

- Phronesis installed ([Installation](Installation.md))
- Basic understanding of BGP ([RFC 4271](https://tools.ietf.org/html/rfc4271))
- Familiarity with RPKI ([RFC 6480](https://tools.ietf.org/html/rfc6480))

---

## Step 1: Project Setup

Create a new policy project:

```bash
mkdir bgp_security
cd bgp_security

# Create policy file
touch security_policy.phr
```

---

## Step 2: Define Constants

Start with essential constants:

```phronesis
# security_policy.phr
# BGP Security Policy for Edge Routers

# Import standard modules
IMPORT Std.RPKI
IMPORT Std.BGP

# ============================================
# Constants
# ============================================

# Bogon prefixes that should never appear in BGP
CONST bogon_prefixes_v4 = [
  "0.0.0.0/8",         # "This" network
  "10.0.0.0/8",        # Private (RFC 1918)
  "100.64.0.0/10",     # Shared address space (RFC 6598)
  "127.0.0.0/8",       # Loopback
  "169.254.0.0/16",    # Link-local
  "172.16.0.0/12",     # Private (RFC 1918)
  "192.0.0.0/24",      # IETF Protocol Assignments
  "192.0.2.0/24",      # TEST-NET-1
  "192.168.0.0/16",    # Private (RFC 1918)
  "198.18.0.0/15",     # Benchmarking
  "198.51.100.0/24",   # TEST-NET-2
  "203.0.113.0/24",    # TEST-NET-3
  "224.0.0.0/4",       # Multicast
  "240.0.0.0/4"        # Reserved
]

# Maximum prefix lengths to accept
CONST max_prefix_len_v4 = 24
CONST max_prefix_len_v6 = 48

# AS path constraints
CONST max_as_path_length = 50

# Our local AS
CONST local_as = 65000
```

---

## Step 3: RPKI Validation Policy

Add RPKI validation as the highest priority:

```phronesis
# ============================================
# RPKI Validation (Highest Priority)
# ============================================

# Reject routes that are RPKI invalid
# These are routes where a ROA exists but doesn't authorize the origin
POLICY rpki_invalid_reject:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI validation failed: origin AS not authorized")
  PRIORITY: 300
```

This policy:
- Checks every route against RPKI
- Rejects only "invalid" routes (ROA exists, wrong origin)
- Allows "not_found" (no ROA coverage) to pass through

For stricter validation:

```phronesis
# Optional: Strict RPKI (also reject not_found)
POLICY rpki_strict:
  Std.RPKI.validate(route) != "valid"
  THEN IF Std.RPKI.validate(route) == "not_found"
       THEN REPORT("Route has no RPKI coverage")
       ELSE REJECT("RPKI invalid")
  PRIORITY: 300
```

---

## Step 4: Bogon Filtering

Filter out bogon prefixes:

```phronesis
# ============================================
# Bogon Filtering
# ============================================

# Reject bogon prefixes
POLICY bogon_filter:
  route.prefix IN bogon_prefixes_v4
  THEN REJECT("Bogon prefix not allowed in global routing")
  PRIORITY: 290
```

---

## Step 5: Prefix Length Filtering

Enforce minimum and maximum prefix lengths:

```phronesis
# ============================================
# Prefix Length Filtering
# ============================================

# Reject too-specific prefixes (longer than /24 for IPv4)
POLICY prefix_too_specific:
  route.prefix_length > max_prefix_len_v4
  AND route.afi == "ipv4"
  THEN REJECT("Prefix too specific: max /" + max_prefix_len_v4)
  PRIORITY: 280

# Reject too-broad prefixes (shorter than /8 for IPv4)
POLICY prefix_too_broad:
  route.prefix_length < 8
  AND route.afi == "ipv4"
  THEN REJECT("Prefix too broad: min /8")
  PRIORITY: 280
```

---

## Step 6: AS Path Validation

Check AS path sanity:

```phronesis
# ============================================
# AS Path Validation
# ============================================

# Reject if AS path is too long
POLICY as_path_too_long:
  Std.BGP.as_path_length(route) > max_as_path_length
  THEN REJECT("AS path too long: max " + max_as_path_length + " ASes")
  PRIORITY: 270

# Reject if our own AS appears in the path (loop prevention)
POLICY as_path_loop:
  Std.BGP.check_loop(route, local_as)
  THEN REJECT("AS path loop detected: own AS in path")
  PRIORITY: 270

# Reject routes with private ASes in path (unless from customers)
POLICY private_as_in_path:
  Std.BGP.get_origin(route) >= 64512
  AND Std.BGP.get_origin(route) <= 65534
  AND route.peer_type != "customer"
  THEN REJECT("Private AS in origin from non-customer")
  PRIORITY: 260
```

---

## Step 7: Community-Based Actions

Handle BGP communities:

```phronesis
# ============================================
# Community-Based Routing
# ============================================

# Well-known communities
CONST BLACKHOLE = "65535:666"
CONST NO_EXPORT = "65535:65281"
CONST NO_ADVERTISE = "65535:65282"

# Handle blackhole community
POLICY blackhole_community:
  Std.BGP.community_contains(route, BLACKHOLE)
  THEN ACCEPT(route WITH {next_hop: "192.0.2.1", blackhole: true})
  PRIORITY: 250

# Log NO_EXPORT routes
POLICY no_export_logging:
  Std.BGP.community_contains(route, NO_EXPORT)
  THEN REPORT({
    event: "no_export_route",
    prefix: route.prefix,
    origin: Std.BGP.get_origin(route)
  })
  PRIORITY: 50
```

---

## Step 8: Peer-Specific Policies

Add policies for different peer types:

```phronesis
# ============================================
# Peer-Specific Policies
# ============================================

# Customer routes get highest local preference
POLICY customer_routes:
  route.peer_type == "customer"
  AND Std.RPKI.validate(route) != "invalid"
  THEN ACCEPT(route WITH {local_pref: 200})
  PRIORITY: 200

# Peer routes get medium local preference
POLICY peer_routes:
  route.peer_type == "peer"
  AND Std.RPKI.validate(route) != "invalid"
  THEN ACCEPT(route WITH {local_pref: 150})
  PRIORITY: 190

# Transit routes get lower local preference
POLICY transit_routes:
  route.peer_type == "transit"
  AND Std.RPKI.validate(route) != "invalid"
  THEN ACCEPT(route WITH {local_pref: 100})
  PRIORITY: 180
```

---

## Step 9: Default Policy

Always have a catch-all:

```phronesis
# ============================================
# Default Policy
# ============================================

# Log and accept any route that passed all filters
POLICY default_accept:
  true
  THEN REPORT({
    event: "route_accepted",
    prefix: route.prefix,
    origin: Std.BGP.get_origin(route),
    rpki: Std.RPKI.validate(route)
  })
  PRIORITY: 1
```

---

## Complete Policy

```phronesis
# security_policy.phr
# Comprehensive BGP Security Policy

IMPORT Std.RPKI
IMPORT Std.BGP

# Constants
CONST bogon_prefixes_v4 = [
  "0.0.0.0/8", "10.0.0.0/8", "100.64.0.0/10", "127.0.0.0/8",
  "169.254.0.0/16", "172.16.0.0/12", "192.0.0.0/24", "192.0.2.0/24",
  "192.168.0.0/16", "198.18.0.0/15", "198.51.100.0/24",
  "203.0.113.0/24", "224.0.0.0/4", "240.0.0.0/4"
]
CONST max_prefix_len_v4 = 24
CONST max_as_path_length = 50
CONST local_as = 65000
CONST BLACKHOLE = "65535:666"

# RPKI Validation
POLICY rpki_invalid:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI invalid")
  PRIORITY: 300

# Bogon Filter
POLICY bogon_filter:
  route.prefix IN bogon_prefixes_v4
  THEN REJECT("Bogon prefix")
  PRIORITY: 290

# Prefix Length
POLICY prefix_length:
  route.prefix_length > max_prefix_len_v4
  THEN REJECT("Prefix too specific")
  PRIORITY: 280

# AS Path Length
POLICY as_path_length:
  Std.BGP.as_path_length(route) > max_as_path_length
  THEN REJECT("AS path too long")
  PRIORITY: 270

# Loop Prevention
POLICY as_loop:
  Std.BGP.check_loop(route, local_as)
  THEN REJECT("AS loop")
  PRIORITY: 270

# Blackhole
POLICY blackhole:
  Std.BGP.community_contains(route, BLACKHOLE)
  THEN ACCEPT(route WITH {blackhole: true})
  PRIORITY: 250

# Default
POLICY default:
  true
  THEN ACCEPT(route)
  PRIORITY: 1
```

---

## Testing

### Test Valid Route

```bash
phronesis run security_policy.phr \
  --route '{
    "prefix": "8.8.8.0/24",
    "prefix_length": 24,
    "origin_as": 15169,
    "as_path": [15169],
    "afi": "ipv4"
  }'
```

Expected: `ACCEPT`

### Test Bogon

```bash
phronesis run security_policy.phr \
  --route '{
    "prefix": "10.0.0.0/24",
    "prefix_length": 24,
    "origin_as": 65001,
    "as_path": [65001],
    "afi": "ipv4"
  }'
```

Expected: `REJECT (Bogon prefix)`

### Test Too Specific

```bash
phronesis run security_policy.phr \
  --route '{
    "prefix": "8.8.8.0/28",
    "prefix_length": 28,
    "origin_as": 15169,
    "as_path": [15169],
    "afi": "ipv4"
  }'
```

Expected: `REJECT (Prefix too specific)`

---

## Best Practices

1. **Order by priority**: Higher numbers = evaluated first
2. **Reject explicitly**: Don't rely on implicit rejection
3. **Log important events**: Use REPORT for auditing
4. **Test thoroughly**: Verify each policy with edge cases
5. **Use RPKI**: Always validate origin authorization
6. **Keep it simple**: Avoid overly complex conditions

---

## Next Steps

- [Tutorial: RPKI](Tutorial-RPKI.md) - Deep dive into RPKI
- [Tutorial: Consensus](Tutorial-Consensus.md) - Multi-party approval
- [Std.BGP](Stdlib-BGP.md) - Complete BGP module reference
- [Std.RPKI](Stdlib-RPKI.md) - Complete RPKI module reference
