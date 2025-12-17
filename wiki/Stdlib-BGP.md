# Std.BGP

Border Gateway Protocol (BGP) operations module.

---

## Overview

The BGP module provides functions for inspecting and manipulating BGP route attributes. It enables policies to make decisions based on AS paths, communities, and other BGP attributes.

---

## Import

```phronesis
IMPORT Std.BGP
```

Or with alias:

```phronesis
IMPORT Std.BGP AS bgp
```

---

## Functions

### extract_as_path

Extract the AS path from a route announcement.

**Signature:**
```
Std.BGP.extract_as_path(route) -> List<Integer>
```

**Parameters:**
- `route` - Route record with BGP attributes

**Returns:**
List of AS numbers in path order (origin AS last).

**Example:**
```phronesis
POLICY as_path_check:
  65000 IN Std.BGP.extract_as_path(route)
  THEN REJECT("Filtered AS in path")
  PRIORITY: 150
```

---

### get_origin

Get the origin AS (the AS that originated the route).

**Signature:**
```
Std.BGP.get_origin(route) -> Integer
```

**Parameters:**
- `route` - Route record

**Returns:**
Origin AS number (last AS in the path).

**Example:**
```phronesis
POLICY origin_filter:
  Std.BGP.get_origin(route) IN blocked_asns
  THEN REJECT("Blocked origin AS")
  PRIORITY: 180
```

---

### as_path_length

Get the length of the AS path.

**Signature:**
```
Std.BGP.as_path_length(route) -> Integer
```

**Parameters:**
- `route` - Route record

**Returns:**
Number of ASes in the path.

**Example:**
```phronesis
CONST max_path_length = 50

POLICY path_length_limit:
  Std.BGP.as_path_length(route) > max_path_length
  THEN REJECT("AS path too long")
  PRIORITY: 170
```

---

### check_loop

Check if the local AS appears in the path (loop detection).

**Signature:**
```
Std.BGP.check_loop(route, local_as) -> Boolean
```

**Parameters:**
- `route` - Route record
- `local_as` - Local AS number to check for

**Returns:**
- `true` - Local AS appears in path (loop detected)
- `false` - No loop

**Example:**
```phronesis
CONST my_as = 65001

POLICY loop_detection:
  Std.BGP.check_loop(route, my_as)
  THEN REJECT("AS path loop detected")
  PRIORITY: 200
```

---

### community_contains

Check if a route has a specific BGP community.

**Signature:**
```
Std.BGP.community_contains(route, community) -> Boolean
```

**Parameters:**
- `route` - Route record
- `community` - Community string (e.g., "65000:100")

**Returns:**
- `true` - Route has the community
- `false` - Route doesn't have the community

**Example:**
```phronesis
POLICY blackhole_community:
  Std.BGP.community_contains(route, "65535:666")
  THEN REJECT("Blackhole community - dropping")
  PRIORITY: 250
```

---

### get_communities

Get all communities attached to a route.

**Signature:**
```
Std.BGP.get_communities(route) -> List<String>
```

**Parameters:**
- `route` - Route record

**Returns:**
List of community strings.

**Example:**
```phronesis
POLICY log_communities:
  Std.BGP.get_communities(route) != []
  THEN REPORT({
    event: "route_with_communities",
    prefix: route.prefix,
    communities: Std.BGP.get_communities(route)
  })
  PRIORITY: 10
```

---

### get_local_pref

Get the LOCAL_PREF attribute.

**Signature:**
```
Std.BGP.get_local_pref(route) -> Integer | null
```

**Parameters:**
- `route` - Route record

**Returns:**
LOCAL_PREF value or null if not set.

**Example:**
```phronesis
POLICY prefer_high_local_pref:
  Std.BGP.get_local_pref(route) >= 200
  THEN ACCEPT(route)
  PRIORITY: 100
```

---

### get_med

Get the Multi-Exit Discriminator (MED) attribute.

**Signature:**
```
Std.BGP.get_med(route) -> Integer | null
```

**Parameters:**
- `route` - Route record

**Returns:**
MED value or null if not set.

**Example:**
```phronesis
POLICY med_filter:
  Std.BGP.get_med(route) > 1000
  THEN REJECT("MED too high")
  PRIORITY: 80
```

---

### get_next_hop

Get the NEXT_HOP attribute.

**Signature:**
```
Std.BGP.get_next_hop(route) -> IPAddress
```

**Parameters:**
- `route` - Route record

**Returns:**
Next hop IP address.

**Example:**
```phronesis
CONST valid_next_hops = ["192.0.2.1", "192.0.2.2"]

POLICY next_hop_filter:
  NOT (Std.BGP.get_next_hop(route) IN valid_next_hops)
  THEN REJECT("Invalid next hop")
  PRIORITY: 160
```

---

### is_ebgp

Check if route was learned via eBGP.

**Signature:**
```
Std.BGP.is_ebgp(route) -> Boolean
```

**Parameters:**
- `route` - Route record

**Returns:**
- `true` - Route from external peer
- `false` - Route from internal peer (iBGP)

**Example:**
```phronesis
POLICY ebgp_only:
  NOT Std.BGP.is_ebgp(route)
  THEN REJECT("iBGP routes not accepted here")
  PRIORITY: 190
```

---

### prepend_count

Count AS prepends (consecutive repeated ASes).

**Signature:**
```
Std.BGP.prepend_count(route) -> Integer
```

**Parameters:**
- `route` - Route record

**Returns:**
Number of AS prepends detected.

**Example:**
```phronesis
POLICY excessive_prepend:
  Std.BGP.prepend_count(route) > 5
  THEN REJECT("Excessive AS prepending")
  PRIORITY: 140
```

---

## Route Record Structure

The route record typically contains:

```phronesis
route = {
  prefix: "10.0.0.0/24",
  prefix_length: 24,
  origin_as: 65001,
  as_path: [65003, 65002, 65001],
  next_hop: "192.0.2.1",
  local_pref: 100,
  med: 50,
  communities: ["65001:100", "65001:200"],
  afi: "ipv4",              # or "ipv6"
  origin: "igp",            # igp, egp, incomplete
  peer_as: 65003,
  peer_ip: "192.0.2.100"
}
```

---

## Common Patterns

### AS Path Filtering

```phronesis
CONST blocked_asns = [64496, 64497, 64498]
CONST max_path_len = 50

POLICY as_path_filter:
  Std.BGP.as_path_length(route) > max_path_len
  OR Std.BGP.get_origin(route) IN blocked_asns
  THEN REJECT("AS path policy violation")
  PRIORITY: 170
```

### Community-Based Routing

```phronesis
# Well-known communities
CONST NO_EXPORT = "65535:65281"
CONST NO_ADVERTISE = "65535:65282"
CONST BLACKHOLE = "65535:666"

POLICY handle_communities:
  Std.BGP.community_contains(route, BLACKHOLE)
  THEN REJECT("Blackhole community")
  PRIORITY: 250

POLICY no_export_handling:
  Std.BGP.community_contains(route, NO_EXPORT)
  THEN ACCEPT(route WITH {export: false})
  PRIORITY: 200
```

### Peer-Specific Policies

```phronesis
CONST tier1_asns = [174, 701, 1299, 2914, 3257, 3356, 6453, 6762]

POLICY tier1_routes:
  Std.BGP.get_origin(route) IN tier1_asns
  THEN ACCEPT(route WITH {local_pref: 150})
  PRIORITY: 120

POLICY customer_routes:
  route.peer_type == "customer"
  THEN ACCEPT(route WITH {local_pref: 200})
  PRIORITY: 130
```

### Loop Prevention

```phronesis
CONST my_as = 65001

POLICY loop_prevention:
  Std.BGP.check_loop(route, my_as)
  THEN REJECT("Own AS in path - loop prevention")
  PRIORITY: 300
```

---

## Best Practices

### 1. Always Check Path Length

```phronesis
# Protect against path manipulation attacks
POLICY path_sanity:
  Std.BGP.as_path_length(route) > 100
  THEN REJECT("Unreasonably long AS path")
  PRIORITY: 200
```

### 2. Validate Origin

```phronesis
# Combine with RPKI for best security
POLICY origin_validation:
  NOT Std.RPKI.check_origin(route)
  AND Std.BGP.get_origin(route) NOT IN trusted_origins
  THEN REJECT("Unverified origin")
  PRIORITY: 180
```

### 3. Use Communities Consistently

```phronesis
# Document your community schema
# 65001:1xxx - Informational
# 65001:2xxx - Actions
# 65001:3xxx - Regions

POLICY community_actions:
  Std.BGP.community_contains(route, "65001:2001")
  THEN ACCEPT(route WITH {local_pref: 50})
  PRIORITY: 100
```

---

## Testing

```elixir
defmodule BGPTest do
  use ExUnit.Case

  test "extracts AS path" do
    route = %{as_path: [65003, 65002, 65001]}
    assert Phronesis.Stdlib.StdBGP.extract_as_path(route) == [65003, 65002, 65001]
  end

  test "gets origin AS" do
    route = %{as_path: [65003, 65002, 65001]}
    assert Phronesis.Stdlib.StdBGP.get_origin(route) == 65001
  end

  test "detects loop" do
    route = %{as_path: [65003, 65001, 65002]}
    assert Phronesis.Stdlib.StdBGP.check_loop(route, 65001) == true
  end

  test "checks community" do
    route = %{communities: ["65000:100", "65000:200"]}
    assert Phronesis.Stdlib.StdBGP.community_contains(route, "65000:100") == true
    assert Phronesis.Stdlib.StdBGP.community_contains(route, "65000:300") == false
  end
end
```

---

## See Also

- [RFC 4271](https://tools.ietf.org/html/rfc4271) - BGP-4 Specification
- [RFC 7454](https://tools.ietf.org/html/rfc7454) - BGP Operations and Security
- [RFC 1997](https://tools.ietf.org/html/rfc1997) - BGP Communities
- [Std.RPKI](Stdlib-RPKI.md) - RPKI validation
- [Tutorial: BGP Security](Tutorial-BGP-Security.md) - BGP security tutorial
