# Architecture Overview

High-level system architecture of the Phronesis policy language.

---

## System Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                        Phronesis System                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐  │
│  │  Source  │───>│  Lexer   │───>│  Parser  │───>│   AST    │  │
│  │  Code    │    │          │    │          │    │          │  │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘  │
│                                                       │         │
│                                                       v         │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                    Interpreter                            │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐       │  │
│  │  │   State     │  │  Evaluator  │  │   Action    │       │  │
│  │  │  Manager    │  │             │  │  Executor   │       │  │
│  │  └─────────────┘  └─────────────┘  └─────────────┘       │  │
│  └──────────────────────────────────────────────────────────┘  │
│                            │                                    │
│                            v                                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                  Standard Library                         │  │
│  │  ┌────────┐  ┌────────┐  ┌───────────┐  ┌──────────┐     │  │
│  │  │Std.RPKI│  │Std.BGP │  │Std.Consens│  │Std.Tempor│     │  │
│  │  └────────┘  └────────┘  └───────────┘  └──────────┘     │  │
│  └──────────────────────────────────────────────────────────┘  │
│                            │                                    │
│                            v                                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                   Consensus Layer                         │  │
│  │  ┌─────────────────────────────────────────────────────┐ │  │
│  │  │                    Raft                              │ │  │
│  │  │  ┌────────┐  ┌────────┐  ┌────────┐  ┌────────┐     │ │  │
│  │  │  │ Leader │  │  Log   │  │  RPC   │  │Snapshot│     │ │  │
│  │  │  │Election│  │Replicat│  │Transprt│  │        │     │ │  │
│  │  │  └────────┘  └────────┘  └────────┘  └────────┘     │ │  │
│  │  └─────────────────────────────────────────────────────┘ │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
                               │
                               v
┌─────────────────────────────────────────────────────────────────┐
│                      External Systems                            │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌───────────┐  │
│  │   RPKI     │  │   Router   │  │  Other     │  │ Monitoring│  │
│  │ Validators │  │  Daemons   │  │   Nodes    │  │  Systems  │  │
│  └────────────┘  └────────────┘  └────────────┘  └───────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Component Overview

### 1. Frontend (Lexer + Parser)

The frontend transforms source code into an Abstract Syntax Tree:

```
Source Code → Tokens → AST
```

- **Lexer**: Tokenizes input into keywords, identifiers, literals
- **Parser**: LL(1) recursive descent parser producing AST
- **AST**: Typed tree representation of the program

### 2. Interpreter

The interpreter executes AST nodes following operational semantics:

- **State Manager**: Manages PolicyTable, ConsensusLog, Environment
- **Evaluator**: Evaluates expressions and conditions
- **Action Executor**: Executes ACCEPT/REJECT/REPORT/EXECUTE

### 3. Standard Library

Built-in modules for network operations:

- **Std.RPKI**: RPKI validation
- **Std.BGP**: BGP route operations
- **Std.Consensus**: Distributed voting
- **Std.Temporal**: Time-based constraints

### 4. Consensus Layer

Distributed agreement using Raft:

- **Leader Election**: Single leader per term
- **Log Replication**: Distributed state machine
- **RPC Transport**: Inter-node communication
- **Snapshotting**: Log compaction

---

## Data Flow

### Policy Execution Flow

```
1. Load Policy
   ├── Lexer tokenizes source
   ├── Parser builds AST
   └── Policies registered in PolicyTable

2. Route Event
   ├── Context created with route data
   └── Environment populated

3. Policy Evaluation
   ├── Policies sorted by priority (descending)
   ├── Each policy's condition evaluated
   └── First matching policy selected

4. Action Execution
   ├── Consensus required (if configured)
   ├── Action executed
   └── Result logged to ConsensusLog

5. Result
   └── ACCEPT/REJECT/REPORT returned
```

### Consensus Flow

```
1. Action Proposed
   └── Client sends to leader

2. Log Append
   ├── Leader appends to local log
   └── Leader replicates to followers

3. Voting
   ├── Followers vote on entry
   └── Votes collected by leader

4. Commit
   ├── Majority reached
   ├── Entry committed
   └── Followers notified

5. Apply
   └── All nodes apply committed entry
```

---

## Module Structure

```
lib/phronesis/
├── phronesis.ex           # Main API
├── application.ex         # OTP Application
├── lexer.ex               # Tokenizer
├── parser.ex              # LL(1) Parser
├── ast.ex                 # AST Node Definitions
├── interpreter.ex         # Execution Engine
├── state.ex               # State Management
├── token.ex               # Token Types
├── cli.ex                 # Command Line Interface
├── stdlib/
│   ├── module.ex          # Module Behaviour
│   ├── rpki.ex            # Std.RPKI
│   ├── rpki_validator.ex  # RPKI Validator Client
│   ├── bgp.ex             # Std.BGP
│   ├── consensus.ex       # Std.Consensus
│   └── temporal.ex        # Std.Temporal
└── consensus/
    ├── raft.ex            # Raft Implementation
    ├── raft/
    │   ├── log.ex         # Raft Log
    │   └── rpc.ex         # RPC Transport
    └── supervisor.ex      # Consensus Supervisor
```

---

## State Model

### Core State

```elixir
%Phronesis.State{
  policy_table: %{},        # name => policy
  consensus_log: [],        # append-only [(action, result, votes)]
  environment: %{},         # name => value
  pending_actions: [],      # actions awaiting consensus
  agents: [],               # consensus participants
  consensus_threshold: 0.67,
  modules: %{}              # registered modules
}
```

### State Transitions

```
Initial State (S0)
      │
      v
┌─────────────────────┐
│   Load Policies     │
│   S0 → S1           │
└─────────────────────┘
      │
      v
┌─────────────────────┐
│   Route Event       │
│   Create Context    │
└─────────────────────┘
      │
      v
┌─────────────────────┐
│ Evaluate Conditions │
│ (pure, no mutation) │
└─────────────────────┘
      │
      v
┌─────────────────────┐
│  Execute Action     │
│  S1 → S2            │
│  (log appended)     │
└─────────────────────┘
      │
      v
┌─────────────────────┐
│  Return Result      │
└─────────────────────┘
```

---

## Security Architecture

### Layers of Defense

```
┌─────────────────────────────────────────┐
│           Grammar Restrictions           │  No I/O primitives
├─────────────────────────────────────────┤
│           Module Gating                  │  Only registered modules
├─────────────────────────────────────────┤
│           Capability System              │  Per-operation permissions
├─────────────────────────────────────────┤
│           Sandbox Isolation              │  No system access
├─────────────────────────────────────────┤
│           Consensus Gating               │  Multi-party approval
└─────────────────────────────────────────┘
```

### Capability Model

```
Policy P requires capabilities C
Module M requires capability C_m
Operation O requires capability C_o

Execute O only if:
  C_o ⊆ C AND C_m ⊆ C
```

---

## Concurrency Model

### BEAM Foundation

Phronesis runs on the Erlang BEAM VM:

- **Processes**: Lightweight isolated processes
- **Supervision**: Fault-tolerant process trees
- **Distribution**: Native clustering support
- **Preemption**: Fair scheduling

### Process Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Application Supervisor                    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────┐  │
│  │  Interpreter │  │   Registry   │  │    Consensus     │  │
│  │    Pool      │  │              │  │   Supervisor     │  │
│  └──────────────┘  └──────────────┘  └──────────────────┘  │
│         │                                      │            │
│         v                                      v            │
│  ┌──────────────┐                    ┌──────────────────┐  │
│  │   Worker 1   │                    │      Raft        │  │
│  │   Worker 2   │                    │    (GenServer)   │  │
│  │   Worker N   │                    │                  │  │
│  └──────────────┘                    └──────────────────┘  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Extension Points

### Custom Modules

```elixir
defmodule MyModule do
  @behaviour Phronesis.Stdlib.Module

  @impl true
  def module_name, do: "My.Custom"

  @impl true
  def required_capability, do: :custom_ops

  @impl true
  def call(args) do
    # Implementation
  end
end

# Register
Phronesis.register_module(MyModule)
```

### Custom Validators

```elixir
defmodule MyValidator do
  @behaviour Phronesis.Stdlib.StdRPKI.Validator

  @impl true
  def validate(prefix, origin_as) do
    # Custom validation logic
    :valid | :invalid | :not_found
  end
end
```

---

## Performance Characteristics

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Tokenize | O(n) | O(n) |
| Parse | O(n) | O(n) |
| Evaluate expr | O(d) | O(d) |
| Policy match | O(p) | O(1) |
| Consensus | O(n) | O(log) |

Where:
- n = input size
- d = expression depth
- p = number of policies
- log = consensus log size

### Benchmarks (Target)

| Metric | v0.1 | v1.0 Target |
|--------|------|-------------|
| Parse | 1K/s | 1M/s |
| Execute | 10K/s | 2M/s |
| Consensus | 100/s | 100K/s |

---

## Deployment Models

### Standalone

```
┌─────────────────┐
│  Single Node    │
│  (all in one)   │
└─────────────────┘
```

### Clustered

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│     Node 1      │────>│     Node 2      │────>│     Node 3      │
│   (Leader)      │<────│   (Follower)    │<────│   (Follower)    │
└─────────────────┘     └─────────────────┘     └─────────────────┘
```

### Embedded

```
┌─────────────────────────────────────────┐
│           Router Application            │
│  ┌─────────────────────────────────┐   │
│  │      Phronesis (embedded)        │   │
│  └─────────────────────────────────┘   │
└─────────────────────────────────────────┘
```

---

## See Also

- [Architecture-Lexer](Architecture-Lexer.md) - Lexer details
- [Architecture-Parser](Architecture-Parser.md) - Parser details
- [Architecture-Interpreter](Architecture-Interpreter.md) - Interpreter details
- [Architecture-Consensus](Architecture-Consensus.md) - Raft implementation
- [Formal Semantics](Formal-Semantics.md) - Mathematical specification
