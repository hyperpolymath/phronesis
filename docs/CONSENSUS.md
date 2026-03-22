# Phronesis Distributed Consensus

## Overview

Phronesis uses **Ra** (Erlang Raft implementation) for distributed consensus across multiple nodes. This enables Byzantine fault-tolerant policy voting in production deployments.

## Architecture

### Components

1. **Consensus.Server** - GenServer wrapper around Ra cluster
2. **Consensus.Server.Machine** - Ra state machine for vote processing
3. **Stdlib.Consensus** - High-level consensus API with automatic fallback

### Consensus Modes

**Mock Mode (Default)**
- Single-node operation
- Simulated voting for development/testing
- No distributed dependencies

**Distributed Mode**
- Multi-node Raft cluster
- Real consensus with leader election
- Replicated log across nodes
- Automatic failover

## Running a Distributed Cluster

### Environment Variables

```bash
# Enable distributed consensus
export PHRONESIS_CONSENSUS_ENABLED=true

# Set unique node ID (node1, node2, node3, etc.)
export PHRONESIS_NODE_ID=node1
```

### 3-Node Cluster Example

**Terminal 1 (Node 1 - Leader):**
```bash
PHRONESIS_CONSENSUS_ENABLED=true \
PHRONESIS_NODE_ID=node1 \
iex --sname node1 --cookie phronesis_cluster -S mix
```

**Terminal 2 (Node 2):**
```bash
PHRONESIS_CONSENSUS_ENABLED=true \
PHRONESIS_NODE_ID=node2 \
iex --sname node2 --cookie phronesis_cluster -S mix
```

**Terminal 3 (Node 3):**
```bash
PHRONESIS_CONSENSUS_ENABLED=true \
PHRONESIS_NODE_ID=node3 \
iex --sname node3 --cookie phronesis_cluster -S mix
```

### Automated Demo Script

```bash
./examples/consensus_cluster_demo.sh
```

This script starts a 3-node cluster automatically.

## API Usage

###Submitting a Vote

```elixir
# Vote on a policy action
{:ok, consensus_achieved, votes} =
  Phronesis.Consensus.Server.vote(
    {:accept, "Allow BGP route from AS64512"},
    ["agent1", "agent2", "agent3"],
    0.67  # 67% threshold
  )

# Result:
# consensus_achieved: true/false
# votes: [{"agent1", true}, {"agent2", true}, {"agent3", false}]
```

### Querying Consensus Log

```elixir
# Get append-only consensus log
{:ok, log} = Phronesis.Consensus.Server.get_log()

# Each entry contains:
# %{
#   action: {:accept, "..."},
#   votes: [{"agent1", true}, ...],
#   result: :approved | :rejected,
#   threshold: 0.67,
#   timestamp: ~U[2026-01-30 ...]
# }
```

### Cluster Status

```elixir
{:ok, status} = Phronesis.Consensus.Server.status()

# Returns:
# %{
#   node_id: :node1,
#   server_id: {:node1, :nonode@nohost},
#   cluster_name: :phronesis_consensus,
#   state: :leader | :follower | :candidate,
#   commit_index: 42,
#   machine_version: 0,
#   members: [{:node1, :nonode@nohost}, {:node2, ...}]
# }
```

### Adding Members

```elixir
# Add a new node to the cluster
:ok = Phronesis.Consensus.Server.add_member(:node4)
```

## Stdlib Integration

The `Phronesis.Stdlib.Consensus` module automatically uses distributed consensus when available:

```elixir
# Automatically uses Raft if PHRONESIS_CONSENSUS_ENABLED=true
# Falls back to mock consensus otherwise
{:ok, consensus_achieved, votes} =
  Phronesis.Stdlib.Consensus.vote(action, agents, threshold)
```

## Data Persistence

Consensus data is stored in `priv/consensus_data/<node_id>/`:

```
priv/consensus_data/
├── node1/          # Ra data for node 1
│   ├── snapshots/
│   └── wal/        # Write-ahead log
├── node2/
└── node3/
```

**Important:** Ensure this directory is persisted in production deployments.

## Raft Consensus Properties

### Leader Election
- Automatic leader election on startup
- Re-election on leader failure
- Typical election time: < 1 second

### Log Replication
- All writes go through the leader
- Replicated to majority of nodes before commit
- Strong consistency guarantees

### Fault Tolerance
- Tolerates `(N-1)/2` node failures (N = cluster size)
- 3-node cluster: tolerates 1 failure
- 5-node cluster: tolerates 2 failures

### Byzantine Fault Tolerance
While Raft provides crash fault tolerance, true Byzantine fault tolerance requires:
1. Minimum 3f+1 nodes (f = Byzantine nodes)
2. Additional validation layers (crypto signatures, etc.)
3. This is Phase 3 future work

## Testing

### Unit Tests

```bash
# Mock consensus tests (always run)
mix test test/consensus_test.exs

# Distributed tests (tagged :skip by default)
mix test --include skip test/consensus_test.exs
```

### Integration Tests

Run the demo script and interact with the cluster:

```bash
./examples/consensus_cluster_demo.sh

# In another terminal:
iex --sname client --remsh node1@localhost --cookie phronesis_cluster

# Submit votes:
Phronesis.Consensus.Server.vote({:accept, "Test"}, ["a1", "a2", "a3"], 0.67)
```

## Production Deployment

### Docker Compose Example

```yaml
version: '3'
services:
  node1:
    image: phronesis:latest
    environment:
      PHRONESIS_CONSENSUS_ENABLED: "true"
      PHRONESIS_NODE_ID: "node1"
      RELEASE_NODE: "node1@phronesis-node1"
      RELEASE_COOKIE: "${CLUSTER_COOKIE}"
    volumes:
      - node1_data:/app/priv/consensus_data

  node2:
    image: phronesis:latest
    environment:
      PHRONESIS_CONSENSUS_ENABLED: "true"
      PHRONESIS_NODE_ID: "node2"
      RELEASE_NODE: "node2@phronesis-node2"
      RELEASE_COOKIE: "${CLUSTER_COOKIE}"
    volumes:
      - node2_data:/app/priv/consensus_data

  node3:
    image: phronesis:latest
    environment:
      PHRONESIS_CONSENSUS_ENABLED: "true"
      PHRONESIS_NODE_ID: "node3"
      RELEASE_NODE: "node3@phronesis-node3"
      RELEASE_COOKIE: "${CLUSTER_COOKIE}"
    volumes:
      - node3_data:/app/priv/consensus_data

volumes:
  node1_data:
  node2_data:
  node3_data:
```

### Kubernetes Example

See `deploy/kubernetes/consensus-statefulset.yaml` for a production-ready StatefulSet configuration.

## Monitoring

### Metrics to Track

- **Commit Index**: Current committed log position
- **Leader Changes**: Frequency of leader elections
- **Vote Latency**: Time to achieve consensus
- **Node Availability**: Uptime of cluster members

### Health Checks

```elixir
# Check if node is healthy
case Phronesis.Consensus.Server.status() do
  {:ok, %{state: :leader}} -> :healthy
  {:ok, %{state: :follower}} -> :healthy
  {:error, _} -> :unhealthy
end
```

## Troubleshooting

### "system_not_started" Error

Ra application not started. Ensure:
```elixir
Application.ensure_all_started(:ra)
```

### Split Brain

If nodes can't communicate:
1. Check network connectivity between nodes
2. Verify node names and cookies match
3. Check firewall rules (EPMD port 4369, distribution ports)

### Data Corruption

If Ra data is corrupted:
```bash
# Stop all nodes
# Delete consensus data
rm -rf priv/consensus_data/*
# Restart cluster
```

## References

- [Ra Documentation](https://github.com/rabbitmq/ra)
- [Raft Paper](https://raft.github.io/raft.pdf)
- [SPEC.core.scm](../SPEC.core.scm) - Phronesis consensus specification

## Future Work

- [ ] Byzantine fault tolerance (PBFT integration)
- [ ] Dynamic membership changes
- [ ] Snapshot compression
- [ ] Metrics export (Prometheus)
- [ ] Admin dashboard for cluster management
