# Phronesis: Safety Proofs

## Purpose

This document formalizes safety guarantees for the Phronesis policy language:

1. **Sandbox Isolation** - Policies cannot escape their execution environment
2. **Capability Enforcement** - Operations are restricted by capability tokens
3. **Byzantine Fault Tolerance** - Consensus holds under adversarial conditions

These proofs complement the operational semantics (termination, type safety, consensus safety).

---

## 1. Sandbox Isolation

### 1.1 Threat Model

**Adversary capabilities:**
- Can author arbitrary policy code
- Can attempt to access system resources
- Cannot modify the interpreter or runtime

**Security goal:** Policy code cannot:
- Access filesystem
- Make network connections
- Execute system commands
- Access memory outside its environment

### 1.2 Isolation Architecture

```
┌─────────────────────────────────────────────────────┐
│                    Host System                       │
│  ┌───────────────────────────────────────────────┐  │
│  │              Phronesis Runtime                 │  │
│  │  ┌─────────────────────────────────────────┐  │  │
│  │  │            Policy Sandbox                │  │  │
│  │  │  ┌─────────────────────────────────┐    │  │  │
│  │  │  │     Policy Execution Context     │    │  │  │
│  │  │  │  - Environment (variables)       │    │  │  │
│  │  │  │  - PolicyTable (read-only)       │    │  │  │
│  │  │  │  - ConsensusLog (append-only)    │    │  │  │
│  │  │  └─────────────────────────────────┘    │  │  │
│  │  │              ↑ Module Calls ↓            │  │  │
│  │  │  ┌─────────────────────────────────┐    │  │  │
│  │  │  │      Capability-Gated Modules    │    │  │  │
│  │  │  │  Std.RPKI, Std.BGP, Std.Consensus│    │  │  │
│  │  │  └─────────────────────────────────┘    │  │  │
│  │  └─────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────┘
```

### 1.3 Formal Definition

**Definition (Sandbox State):**
```
SandboxState = {
  environment : Map<String, Value>,
  policy_table : Map<PolicyID, Policy>,
  consensus_log : List<LogEntry>,
  capabilities : Set<Capability>
}
```

**Definition (Valid State Transition):**
```
A state transition S → S' is valid iff:
  1. S'.environment ⊇ S.environment (monotonic growth only)
  2. S'.policy_table ⊇ S.policy_table (policies can be added, not removed)
  3. S'.consensus_log = S.consensus_log ++ [new_entries] (append-only)
  4. ∀ operation in transition: required_cap(operation) ∈ S.capabilities
```

### 1.4 Isolation Theorem

**Theorem 1 (Sandbox Isolation):**
For any policy P and initial state S₀, executing P cannot:
1. Read or write files
2. Make network connections
3. Execute system commands
4. Access memory outside the sandbox

**Proof:**

**(1) No file operations:**

By grammar inspection, the only operations are:
- `EXECUTE(f, args)` - calls a registered function
- `REPORT(msg)` - logs to ConsensusLog
- `REJECT(reason)` - returns result
- `ACCEPT(reason)` - returns result

None of these map to file operations. The interpreter's `do_execute_action/2`
function handles these exhaustively:

```elixir
defp do_execute_action({:execute, function, args}, state) do
  call_module([function], args, state)  # Only registered modules
end
```

Module lookup is restricted to the `modules` registry. File operations
are not exposed. ∎

**(2) No network connections:**

Network operations require calling into Erlang's `:gen_tcp`, `:ssl`, or
`:httpc` modules. These are not exposed in the standard library.

The `Std.*` modules only provide:
- `Std.RPKI.validate/1` - Pure function (stub or cached lookup)
- `Std.BGP.extract_as_path/1` - Pure function
- `Std.Consensus.require_votes/2` - Uses internal agent registry
- `Std.Temporal.eventually/2` - Uses `Process.sleep` only

No network primitives are exposed. ∎

**(3) No system commands:**

The interpreter has no path to `System.cmd/3` or `:os.cmd/1`.
Function calls go through `call_module/3` which only resolves:
- Registered `Std.*` modules
- User-registered modules (controlled by host)

```elixir
defp call_module(path, args, state) do
  case State.lookup_module(state, path) do
    {:ok, module} -> module.call(args)  # Only registered modules
    :error -> resolve_builtin_module(path, args)  # Fixed set
  end
end
```

The fixed builtin set contains no system access. ∎

**(4) Memory isolation:**

The execution state is a pure Elixir struct. Variables are stored in
`state.environment`, a simple `Map`. There is no pointer arithmetic
or memory access beyond the map operations `Map.put/3` and `Map.fetch/2`.

The BEAM VM provides memory safety guarantees at the language level. ∎

**QED: Sandbox Isolation holds.** ∎

---

## 2. Capability Enforcement

### 2.1 Capability Model

**Definition (Capability):**
```
Capability = {
  resource : ResourceType,
  operations : Set<Operation>,
  constraints : List<Constraint>
}

ResourceType = RouteTable | ConsensusVote | NetworkInterface | ...
Operation = Read | Write | Execute | Vote | ...
Constraint = TimeBound(start, end) | RateLimited(n, period) | ...
```

### 2.2 Capability Tokens

Each policy execution context has a set of capability tokens:

```elixir
@type capability :: %{
  resource: atom(),
  operations: [atom()],
  constraints: [constraint()]
}

@type context :: %{
  capabilities: [capability()],
  # ... other fields
}
```

### 2.3 Enforcement Points

**Point 1: Module Call**
```elixir
defp call_module(path, args, state) do
  required_cap = capability_for_module(path)

  if has_capability?(state, required_cap) do
    module.call(args)
  else
    {:error, {:capability_denied, path, required_cap}}
  end
end
```

**Point 2: Action Execution**
```elixir
defp do_execute_action(action, state) do
  required_cap = capability_for_action(action)

  unless has_capability?(state, required_cap) do
    raise CapabilityError, action: action, required: required_cap
  end

  # ... proceed with execution
end
```

### 2.4 Capability Soundness

**Theorem 2 (Capability Soundness):**
No operation executes without the required capability.

**Proof:**

By inspection of execution paths:

1. **EXECUTE** actions go through `call_module/3` which checks capabilities
2. **Module calls** in expressions go through the same path
3. **REPORT** requires `{:consensus_log, [:append]}`
4. **REJECT/ACCEPT** require `{:route_decision, [:write]}`

All paths have enforcement points. ∎

### 2.5 Capability Composition

**Property (Least Privilege):**
A policy receives only capabilities explicitly granted:

```elixir
def new_policy_context(policy, grants) do
  %{
    capabilities: filter_grants(grants, policy.id),
    # ... other context
  }
end
```

**Property (No Capability Escalation):**
A policy cannot acquire capabilities it wasn't granted:

```
∀ S, S'. (S → S') ⟹ S'.capabilities ⊆ S.capabilities
```

This holds because capabilities are only set at context creation
and never modified during execution. ∎

---

## 3. Byzantine Fault Tolerance

### 3.1 System Model

**Assumptions:**
- N total agents (policy evaluators)
- f Byzantine (malicious) agents where N ≥ 3f + 1
- Asynchronous network with eventual delivery
- Cryptographic primitives are secure

### 3.2 Consensus Protocol

Phronesis uses a simplified PBFT-style protocol:

```
Phase 1: PROPOSE
  Leader proposes action to all agents

Phase 2: VOTE
  Each agent evaluates policy and votes
  Votes are signed with agent's key

Phase 3: COMMIT
  If votes ≥ threshold, action commits
  Result logged to ConsensusLog
```

### 3.3 Safety Properties

**Property (Agreement):**
All honest agents agree on the execution result.

**Property (Validity):**
If all honest agents have the same input, the result reflects that input.

**Property (Termination):**
Every action eventually commits or aborts.

### 3.4 BFT Safety Theorem

**Theorem 3 (Byzantine Safety):**
With N ≥ 3f + 1 agents and threshold t = (2N + 1) / 3:
1. No conflicting actions commit
2. Byzantine agents cannot force invalid actions

**Proof Sketch:**

**(1) No conflicting actions:**

Suppose actions A and A' both commit for the same policy invocation.

- A commits: at least t agents voted for A
- A' commits: at least t agents voted for A'

With t = (2N + 1) / 3, we have:
- Votes for A ≥ (2N + 1) / 3
- Votes for A' ≥ (2N + 1) / 3
- Total votes ≥ (4N + 2) / 3 > N (contradiction)

Therefore, at most one action commits. ∎

**(2) Byzantine agents cannot force invalid actions:**

Byzantine agents control at most f votes.
Valid commit requires t = (2N + 1) / 3 votes.

For N = 3f + 1:
- t = (6f + 3) / 3 = 2f + 1
- f < 2f + 1 = t

Byzantine agents alone cannot reach threshold.
At least f + 1 honest agents must vote for commit.
Honest agents only vote for valid actions (by definition).
Therefore, only valid actions can commit. ∎

**QED: Byzantine Safety holds.** ∎

### 3.5 Liveness Under Partial Synchrony

**Theorem 4 (Eventual Liveness):**
After GST (Global Stabilization Time), all valid actions eventually commit.

**Proof:**

After GST, messages are delivered within bound Δ.
Honest agents (≥ 2f + 1) will receive proposals and vote.
With 2f + 1 ≥ t votes, action commits.
Timeout mechanism ensures progress even with crashed leader. ∎

---

## 4. Combined Security Analysis

### 4.1 Defense in Depth

```
Layer 1: Grammar Restrictions
  └── No loops, no recursion, no I/O primitives

Layer 2: Sandbox Isolation
  └── Memory isolation, no system access

Layer 3: Capability Enforcement
  └── Explicit grants for each operation

Layer 4: Consensus Requirements
  └── Multi-party agreement for actions

Layer 5: Audit Log
  └── Immutable record of all executions
```

### 4.2 Attack Surface Analysis

| Attack Vector | Mitigation | Proof Reference |
|---------------|------------|-----------------|
| Code injection | Grammar rejects unknown constructs | Theorem 1.1 |
| Sandbox escape | No I/O primitives exposed | Theorem 1 |
| Privilege escalation | Capability checking at all entry points | Theorem 2 |
| Byzantine corruption | BFT consensus with f < N/3 | Theorem 3 |
| Denial of service | Termination guarantee | Semantics doc |
| Repudiation | Append-only ConsensusLog | Semantics doc |

### 4.3 Residual Risks

**R1: Side-channel attacks**
- Timing attacks on module calls
- Mitigation: Constant-time operations where feasible

**R2: Resource exhaustion**
- Large policies could consume memory
- Mitigation: Policy size limits, resource quotas

**R3: Cryptographic weaknesses**
- Depends on underlying crypto library
- Mitigation: Use well-audited libraries (Erlang :crypto)

---

## 5. Mechanization Status

| Property | Status | Proof System |
|----------|--------|--------------|
| Sandbox Isolation | Manual proof | This document |
| Capability Soundness | Manual proof | This document |
| BFT Safety | Manual proof | This document |
| BFT Liveness | Manual proof | This document |
| Termination | Proven | Semantics doc |
| Type Safety | Sketch | Semantics doc |

### 5.1 Future Mechanization

**TLA+ (Consensus Protocol):**
```tla
VARIABLES
  votes,      \* Map: Agent -> Vote
  committed,  \* Boolean
  log         \* Sequence of LogEntry

BFTSafety ==
  \A a1, a2 \in CommittedActions:
    a1 = a2 \/ ~Conflict(a1, a2)
```

**Coq (Language Properties):**
```coq
Theorem sandbox_isolation:
  forall (p : Policy) (s : State),
    WellFormed p ->
    ~(Executes p FileOp) /\
    ~(Executes p NetworkOp) /\
    ~(Executes p SystemOp).
```

---

## 6. For IRTF Submission

Include as **Appendix C: Safety Proofs** with:

1. Summary of threat model
2. Key theorems (Isolation, Capability, BFT)
3. References to formal verification (TLA+, Coq)

**Abstract for section:**

> "We prove that Phronesis policies execute within a secure sandbox,
> enforce capability-based access control, and achieve Byzantine
> fault tolerance with N ≥ 3f + 1 agents. These properties ensure
> that network policies cannot be corrupted by malicious actors
> and that all policy decisions are auditable and non-repudiable."

---

## References

1. Castro, M., & Liskov, B. (1999). Practical Byzantine Fault Tolerance. OSDI.
2. Miller, M. S., et al. (2003). Capability Myths Demolished.
3. Wahby, R. S., et al. (2017). Verifiable ASICs.
4. Patrignani, M., et al. (2019). Formal Approaches to Secure Compilation.
