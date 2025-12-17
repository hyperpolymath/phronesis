# Std.Consensus

Distributed consensus and voting module.

---

## Overview

The Consensus module provides primitives for distributed agreement on policy actions. It implements a Raft-based consensus protocol ensuring that critical network changes require approval from multiple nodes before execution.

---

## Import

```phronesis
IMPORT Std.Consensus
```

---

## Functions

### require_votes

Request votes from agents for an action, returning success if threshold met.

**Signature:**
```
Std.Consensus.require_votes(action, threshold: Float) -> Boolean
```

**Parameters:**
- `action` - The action to vote on
- `threshold` - Required approval percentage (0.0 to 1.0), default 0.51

**Options:**
- `threshold` - Minimum approval ratio (default: 0.51)
- `timeout` - Voting timeout in ms (default: 5000)
- `agents` - Specific agents to query (default: all registered)

**Returns:**
- `true` - Threshold met, action approved
- `false` - Threshold not met, action rejected

**Example:**
```phronesis
POLICY consensus_required:
  route.is_critical == true
  THEN IF Std.Consensus.require_votes(ACCEPT(route), threshold: 0.67)
       THEN ACCEPT(route)
       ELSE REJECT("Consensus not reached")
  PRIORITY: 100
```

---

### propose

Propose a command through Raft consensus.

**Signature:**
```
Std.Consensus.propose(command) -> {ok: index} | {error: reason}
```

**Parameters:**
- `command` - Command to propose

**Returns:**
- `{ok: index}` - Command accepted, returns log index
- `{error: reason}` - Command rejected

**Example:**
```phronesis
POLICY log_decision:
  true
  THEN IF Std.Consensus.propose({action: "accept", route: route}).ok != null
       THEN ACCEPT(route)
       ELSE REPORT("Failed to log decision")
  PRIORITY: 50
```

---

### get_leader

Get the current Raft leader's identifier.

**Signature:**
```
Std.Consensus.get_leader() -> String | null
```

**Returns:**
- Leader node ID if a leader exists
- `null` if no leader (election in progress)

**Example:**
```phronesis
POLICY leader_check:
  Std.Consensus.get_leader() == null
  THEN REPORT("Warning: No consensus leader")
  PRIORITY: 10
```

---

### is_leader

Check if the current node is the Raft leader.

**Signature:**
```
Std.Consensus.is_leader() -> Boolean
```

**Returns:**
- `true` - Current node is leader
- `false` - Current node is follower or candidate

**Example:**
```phronesis
POLICY leader_only_action:
  Std.Consensus.is_leader()
  AND route.requires_leader == true
  THEN EXECUTE(leader_action, route)
  PRIORITY: 100
```

---

### cluster_state

Get the current cluster state.

**Signature:**
```
Std.Consensus.cluster_state() -> Record
```

**Returns:**
```phronesis
{
  leader: "node1",
  term: 5,
  commit_index: 1234,
  nodes: ["node1", "node2", "node3"],
  state: "leader"  # or "follower", "candidate"
}
```

**Example:**
```phronesis
POLICY cluster_health:
  Std.Consensus.cluster_state().nodes < 3
  THEN REPORT("Warning: Cluster degraded")
  PRIORITY: 5
```

---

## Consensus Protocol

### Overview

Phronesis uses Raft consensus with these guarantees:

1. **Leader Election**: Single leader per term
2. **Log Replication**: All committed entries replicated to majority
3. **Safety**: Committed entries never lost
4. **Liveness**: Progress after network partition heals

### Protocol Flow

```
1. PROPOSE
   Client ──────> Leader

2. APPEND
   Leader ──────> Followers

3. VOTE
   Followers ───> Leader

4. COMMIT
   Leader ──────> Followers

5. APPLY
   All nodes apply committed entry
```

### Threshold Calculation

Default Byzantine fault tolerance threshold:

```
threshold = (2N + 1) / 3

N = 3:  threshold = 2.33 → need 3 of 3
N = 5:  threshold = 3.67 → need 4 of 5
N = 7:  threshold = 5.00 → need 5 of 7
```

For simple majority:
```
threshold = 0.51 → need N/2 + 1
```

---

## Configuration

### Cluster Setup

```elixir
# config/config.exs
config :phronesis, Phronesis.Consensus.Raft,
  node_id: "node1",
  peers: ["node2", "node3"],
  election_timeout: {150, 300},  # min, max ms
  heartbeat_interval: 50,        # ms
  snapshot_threshold: 10000      # entries before snapshot
```

### Environment Variables

```bash
export PHRONESIS_NODE_ID=node1
export PHRONESIS_PEERS=node2,node3
export PHRONESIS_CONSENSUS_THRESHOLD=0.67
```

---

## Common Patterns

### Two-Phase Accept

```phronesis
POLICY two_phase_accept:
  route.prefix IN critical_prefixes
  THEN IF Std.Consensus.require_votes(ACCEPT(route), threshold: 0.67)
       THEN ACCEPT(route)
       ELSE REJECT("Consensus required for critical prefix")
  PRIORITY: 150
```

### Consensus with Fallback

```phronesis
POLICY consensus_with_fallback:
  route.requires_consensus == true
  THEN IF Std.Consensus.get_leader() != null
       THEN IF Std.Consensus.require_votes(ACCEPT(route))
            THEN ACCEPT(route)
            ELSE REJECT("Consensus denied")
       ELSE REPORT("Operating without consensus - leader unavailable")
  PRIORITY: 100
```

### Audit Trail

```phronesis
POLICY audit_all_decisions:
  true
  THEN IF Std.Consensus.propose({
         action: "policy_decision",
         policy: "audit_all_decisions",
         route: route,
         result: "accept"
       }).ok != null
       THEN ACCEPT(route)
       ELSE REJECT("Failed to record decision")
  PRIORITY: 1
```

### Leader-Only Operations

```phronesis
POLICY leader_operations:
  Std.Consensus.is_leader()
  AND route.type == "aggregate"
  THEN EXECUTE(create_aggregate, route)
  PRIORITY: 100
```

---

## Raft Implementation Details

### States

```
┌─────────────┐    election    ┌─────────────┐
│  Follower   │ ─────────────> │  Candidate  │
└─────────────┘                └─────────────┘
      ^                              │
      │        loses election        │
      └──────────────────────────────┤
                                     │ wins election
                                     v
                              ┌─────────────┐
                              │   Leader    │
                              └─────────────┘
```

### Term and Log

```
Term 1:  [entry1] [entry2] [entry3]
Term 2:  [entry4] [entry5]
Term 3:  [entry6] [entry7] [entry8] ...
         ^
         commit_index
```

### Election Safety

- Each node votes once per term
- Candidate needs majority to become leader
- At most one leader per term

### Log Matching

- If two logs have entry with same index and term, they're identical up to that point
- Leader never overwrites its log
- Followers truncate conflicting entries

---

## Failure Handling

### Network Partition

```
Before partition:
  [node1:leader] ─── [node2] ─── [node3]

During partition:
  [node1:leader] ─── [node2]     [node3:isolated]

  Majority (node1, node2) continues operating
  node3 becomes candidate, fails to get votes

After healing:
  [node1:leader] ─── [node2] ─── [node3:follower]

  node3 catches up from leader
```

### Leader Failure

```
1. Leader (node1) fails
2. Followers detect missed heartbeats
3. Timeout triggers election
4. New leader elected (e.g., node2)
5. Clients redirected to new leader
```

### Minority Partition

```
If less than majority available:
- No new commits possible
- Read-only operations may continue
- System waits for partition to heal
```

---

## Monitoring

### Metrics

```elixir
# Get consensus metrics
Phronesis.Stdlib.StdConsensus.cluster_state()
# => %{
#      term: 5,
#      commit_index: 1234,
#      applied_index: 1230,
#      pending_entries: 4,
#      state: :leader
#    }
```

### Health Checks

```phronesis
POLICY health_check:
  Std.Consensus.get_leader() == null
  OR Std.Consensus.cluster_state().nodes < 3
  THEN REPORT({
    event: "consensus_degraded",
    leader: Std.Consensus.get_leader(),
    state: Std.Consensus.cluster_state()
  })
  PRIORITY: 1
```

---

## Testing

### Local Testing

```elixir
# Start a local Raft cluster for testing
{:ok, _} = Phronesis.Consensus.Supervisor.start_link(
  node_id: "test1",
  peers: []
)

# Propose a command
{:ok, index} = Phronesis.Stdlib.StdConsensus.propose(%{test: true})
```

### Integration Testing

```elixir
defmodule ConsensusTest do
  use ExUnit.Case

  test "require_votes returns true with single node" do
    assert Phronesis.Stdlib.StdConsensus.require_votes(
      {:accept, %{prefix: "10.0.0.0/24"}},
      threshold: 0.51
    ) == true
  end

  test "get_leader returns node id" do
    leader = Phronesis.Stdlib.StdConsensus.get_leader()
    assert is_binary(leader) or is_nil(leader)
  end
end
```

---

## See Also

- [Architecture-Consensus](Architecture-Consensus.md) - Raft implementation details
- [Tutorial: Consensus Routing](Tutorial-Consensus.md) - Multi-party approval tutorial
- [Security Model](Security-Model.md) - Byzantine fault tolerance
- [Ongaro 2014](https://raft.github.io/raft.pdf) - Raft paper
