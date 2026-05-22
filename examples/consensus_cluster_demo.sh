#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Multi-node Raft consensus cluster demo for Phronesis

set -e

echo "======================================================================"
echo "Phronesis Distributed Consensus Demo (3-node Raft cluster)"
echo "======================================================================"
echo ""

# Clean up previous runs
echo "Cleaning up previous consensus data..."
rm -rf priv/consensus_data
mkdir -p priv/consensus_data

# Node configuration
NODE1_NAME="node1@localhost"
NODE2_NAME="node2@localhost"
NODE3_NAME="node3@localhost"

NODE1_PORT=4001
NODE2_PORT=4002
NODE3_PORT=4003

echo "Starting 3-node Raft cluster..."
echo "  Node 1: $NODE1_NAME (port $NODE1_PORT)"
echo "  Node 2: $NODE2_NAME (port $NODE2_PORT)"
echo "  Node 3: $NODE3_NAME (port $NODE3_PORT)"
echo ""

# Start node 1 (leader)
echo "Starting node1 (initial leader)..."
PHRONESIS_CONSENSUS_ENABLED=true \
PHRONESIS_NODE_ID=node1 \
iex --sname node1 \
    --cookie phronesis_cluster \
    -S mix run &
NODE1_PID=$!

# Wait for node1 to start
sleep 3

# Start node 2
echo "Starting node2..."
PHRONESIS_CONSENSUS_ENABLED=true \
PHRONESIS_NODE_ID=node2 \
iex --sname node2 \
    --cookie phronesis_cluster \
    -S mix run &
NODE2_PID=$!

# Wait for node2 to start
sleep 2

# Start node 3
echo "Starting node3..."
PHRONESIS_CONSENSUS_ENABLED=true \
PHRONESIS_NODE_ID=node3 \
iex --sname node3 \
    --cookie phronesis_cluster \
    -S mix run &
NODE3_PID=$!

echo ""
echo "All nodes started!"
echo "  Node 1 PID: $NODE1_PID"
echo "  Node 2 PID: $NODE2_PID"
echo "  Node 3 PID: $NODE3_PID"
echo ""
echo "To interact with the cluster:"
echo "  1. Connect to node1: iex --sname client --remsh node1@localhost --cookie phronesis_cluster"
echo "  2. Submit a vote:"
echo "     Phronesis.Consensus.Server.vote({:accept, \"Allow traffic\"}, [\"agent1\", \"agent2\", \"agent3\"], 0.67)"
echo "  3. Check status:"
echo "     Phronesis.Consensus.Server.status()"
echo "  4. View consensus log:"
echo "     Phronesis.Consensus.Server.get_log()"
echo ""
echo "Press Ctrl+C to stop the cluster"
echo ""

# Wait for user to stop
trap "kill $NODE1_PID $NODE2_PID $NODE3_PID 2>/dev/null; exit 0" INT TERM

wait
