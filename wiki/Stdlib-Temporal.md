# Std.Temporal

Time-based constraints and temporal operations module.

---

## Overview

The Temporal module provides functions for time-based policy constraints. It enables policies that depend on time windows, deadlines, and temporal conditions.

---

## Import

```phronesis
IMPORT Std.Temporal
```

Or with alias:

```phronesis
IMPORT Std.Temporal AS time
```

---

## Functions

### within_window

Check if current time is within a time window.

**Signature:**
```
Std.Temporal.within_window(start, end) -> Boolean
```

**Parameters:**
- `start` - Start time (HH:MM format or DateTime)
- `end` - End time (HH:MM format or DateTime)

**Returns:**
- `true` - Current time is within window
- `false` - Current time is outside window

**Example:**
```phronesis
POLICY maintenance_window:
  Std.Temporal.within_window("02:00", "04:00")
  THEN ACCEPT(route WITH {maintenance: true})
  PRIORITY: 50
```

**Notes:**
- Times are in UTC by default
- Windows can cross midnight: `within_window("22:00", "06:00")`
- Full DateTime also supported: `within_window("2025-01-15T00:00:00Z", "2025-01-16T00:00:00Z")`

---

### now

Get the current UTC timestamp.

**Signature:**
```
Std.Temporal.now() -> DateTime
```

**Returns:**
Current UTC DateTime.

**Example:**
```phronesis
POLICY log_timestamp:
  true
  THEN REPORT({
    event: "route_processed",
    timestamp: Std.Temporal.now(),
    route: route
  })
  PRIORITY: 1
```

---

### after

Check if current time is after a specified time.

**Signature:**
```
Std.Temporal.after(datetime) -> Boolean
```

**Parameters:**
- `datetime` - DateTime to compare against

**Returns:**
- `true` - Current time is after specified time
- `false` - Current time is before or equal

**Example:**
```phronesis
CONST cutover_time = 2025-06-01T00:00:00Z

POLICY new_policy_active:
  Std.Temporal.after(cutover_time)
  THEN ACCEPT(route WITH {new_policy: true})
  PRIORITY: 100
```

---

### before

Check if current time is before a specified time.

**Signature:**
```
Std.Temporal.before(datetime) -> Boolean
```

**Parameters:**
- `datetime` - DateTime to compare against

**Returns:**
- `true` - Current time is before specified time
- `false` - Current time is after or equal

**Example:**
```phronesis
CONST deprecation_date = 2025-12-31T23:59:59Z

POLICY legacy_support:
  Std.Temporal.before(deprecation_date)
  AND route.legacy_format == true
  THEN ACCEPT(route)
  PRIORITY: 80
```

---

### day_of_week

Get the current day of week.

**Signature:**
```
Std.Temporal.day_of_week() -> String
```

**Returns:**
Day name: "monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"

**Example:**
```phronesis
POLICY weekend_policy:
  Std.Temporal.day_of_week() IN ["saturday", "sunday"]
  THEN ACCEPT(route WITH {weekend: true})
  PRIORITY: 60
```

---

### hour_of_day

Get the current hour (0-23).

**Signature:**
```
Std.Temporal.hour_of_day() -> Integer
```

**Returns:**
Hour in UTC (0-23).

**Example:**
```phronesis
POLICY business_hours:
  Std.Temporal.hour_of_day() >= 9
  AND Std.Temporal.hour_of_day() < 17
  THEN ACCEPT(route WITH {business_hours: true})
  PRIORITY: 70
```

---

### eventually

Schedule an action to execute before a deadline (future feature).

**Signature:**
```
Std.Temporal.eventually(action, deadline) -> Boolean
```

**Parameters:**
- `action` - Action to schedule
- `deadline` - Deadline DateTime or duration

**Returns:**
- `true` - Action scheduled
- `false` - Could not schedule

**Example:**
```phronesis
POLICY delayed_accept:
  route.delayed == true
  THEN IF Std.Temporal.eventually(ACCEPT(route), deadline: "1h")
       THEN REPORT("Route scheduled for delayed acceptance")
       ELSE REJECT("Could not schedule route")
  PRIORITY: 50
```

**Note:** This function is planned for v0.3.x.

---

### elapsed_since

Calculate time elapsed since a timestamp.

**Signature:**
```
Std.Temporal.elapsed_since(datetime) -> Duration
```

**Parameters:**
- `datetime` - Starting DateTime

**Returns:**
Duration record with seconds, minutes, hours, days.

**Example:**
```phronesis
POLICY stale_route_check:
  Std.Temporal.elapsed_since(route.last_update).hours > 24
  THEN REPORT("Route not updated in over 24 hours")
  PRIORITY: 20
```

---

## Time Formats

### Time of Day (HH:MM)

```phronesis
"00:00"     # Midnight
"06:30"     # 6:30 AM
"12:00"     # Noon
"18:45"     # 6:45 PM
"23:59"     # 11:59 PM
```

### Full DateTime (ISO 8601)

```phronesis
2025-01-15T10:30:00Z           # UTC
2025-01-15T10:30:00+02:00      # With timezone
2025-12-31T23:59:59Z           # End of year
```

### Duration (planned)

```phronesis
"30s"       # 30 seconds
"5m"        # 5 minutes
"1h"        # 1 hour
"24h"       # 24 hours
"7d"        # 7 days
```

---

## Common Patterns

### Maintenance Window

```phronesis
POLICY maintenance_mode:
  Std.Temporal.within_window("02:00", "04:00")
  AND Std.Temporal.day_of_week() == "sunday"
  THEN ACCEPT(route WITH {maintenance: true})
  ELSE IF Std.Temporal.within_window("02:00", "04:00")
       THEN REJECT("Outside maintenance day")
  PRIORITY: 200
```

### Business Hours Routing

```phronesis
CONST business_start = 9
CONST business_end = 17

POLICY business_hours_routing:
  Std.Temporal.hour_of_day() >= business_start
  AND Std.Temporal.hour_of_day() < business_end
  AND NOT (Std.Temporal.day_of_week() IN ["saturday", "sunday"])
  THEN ACCEPT(route WITH {route_type: "primary"})
  ELSE ACCEPT(route WITH {route_type: "backup"})
  PRIORITY: 100
```

### Time-Based Cutover

```phronesis
CONST old_policy_end = 2025-06-30T23:59:59Z
CONST new_policy_start = 2025-07-01T00:00:00Z

POLICY gradual_cutover:
  Std.Temporal.before(old_policy_end)
  THEN ACCEPT(route)  # Old behavior
  ELSE ACCEPT(route WITH {new_rules: true})  # New behavior
  PRIORITY: 100
```

### Rate Limiting by Time

```phronesis
POLICY peak_hours_limiting:
  Std.Temporal.hour_of_day() >= 9
  AND Std.Temporal.hour_of_day() <= 17
  AND route.priority < 100
  THEN REJECT("Low priority routes rejected during peak hours")
  PRIORITY: 150
```

### Scheduled Actions

```phronesis
CONST announcement_time = 2025-03-15T10:00:00Z

POLICY scheduled_announcement:
  Std.Temporal.after(announcement_time)
  AND route.prefix == "203.0.113.0/24"
  THEN ACCEPT(route)
  PRIORITY: 100
```

---

## Timezone Handling

### Default: UTC

All times are UTC by default:

```phronesis
# These are equivalent
Std.Temporal.within_window("02:00", "04:00")
Std.Temporal.within_window("02:00Z", "04:00Z")
```

### Timezone Conversion (Future)

```phronesis
# Planned for v0.3.x
Std.Temporal.in_timezone("America/New_York")
  .within_window("09:00", "17:00")
```

### Best Practice

Always use UTC for policies:

```phronesis
# Good: UTC is explicit and unambiguous
POLICY utc_maintenance:
  Std.Temporal.within_window("02:00", "04:00")  # UTC
  THEN ACCEPT(route)
  PRIORITY: 100

# Add comments for local time reference
# Maintenance: 02:00-04:00 UTC (21:00-23:00 EST)
```

---

## Testing with Time

### Mock Time

For testing, inject a fixed time:

```elixir
# In test setup
Phronesis.Stdlib.StdTemporal.set_mock_time(~U[2025-01-15 03:00:00Z])

# Run tests
assert Phronesis.Stdlib.StdTemporal.within_window("02:00", "04:00") == true

# Clear mock
Phronesis.Stdlib.StdTemporal.clear_mock_time()
```

### Test Examples

```elixir
defmodule TemporalTest do
  use ExUnit.Case

  test "within_window during window" do
    Phronesis.Stdlib.StdTemporal.set_mock_time(~U[2025-01-15 03:00:00Z])
    assert Phronesis.Stdlib.StdTemporal.within_window("02:00", "04:00") == true
  end

  test "within_window outside window" do
    Phronesis.Stdlib.StdTemporal.set_mock_time(~U[2025-01-15 10:00:00Z])
    assert Phronesis.Stdlib.StdTemporal.within_window("02:00", "04:00") == false
  end

  test "within_window crossing midnight" do
    Phronesis.Stdlib.StdTemporal.set_mock_time(~U[2025-01-15 23:30:00Z])
    assert Phronesis.Stdlib.StdTemporal.within_window("22:00", "06:00") == true
  end
end
```

---

## See Also

- [Types](Types.md) - DateTime type details
- [Tutorial: Traffic Engineering](Tutorial-Traffic-Engineering.md) - Time-based routing
- [Formal Semantics](Formal-Semantics.md) - Temporal operators
