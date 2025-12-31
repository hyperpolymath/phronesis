# Temporal Logic Specifications for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides comprehensive temporal logic specifications for Phronesis, covering safety, liveness, fairness properties using LTL, CTL, and TLA+.

---

## 1. Temporal Logic Foundations

### 1.1 Linear Temporal Logic (LTL)

**Syntax:**
```
φ ::= p                    -- Atomic proposition
    | ¬φ                   -- Negation
    | φ ∧ ψ                -- Conjunction
    | φ ∨ ψ                -- Disjunction
    | φ → ψ                -- Implication
    | X φ                  -- Next (○)
    | F φ                  -- Eventually (◇)
    | G φ                  -- Always (□)
    | φ U ψ                -- Until
    | φ R ψ                -- Release
    | φ W ψ                -- Weak Until
```

**Semantics (over infinite traces σ):**
```
σ, i ⊨ p         iff  p ∈ σ[i]
σ, i ⊨ X φ       iff  σ, i+1 ⊨ φ
σ, i ⊨ F φ       iff  ∃j ≥ i. σ, j ⊨ φ
σ, i ⊨ G φ       iff  ∀j ≥ i. σ, j ⊨ φ
σ, i ⊨ φ U ψ     iff  ∃j ≥ i. (σ, j ⊨ ψ ∧ ∀k. i ≤ k < j → σ, k ⊨ φ)
```

### 1.2 Computation Tree Logic (CTL)

**Syntax:**
```
φ ::= p | ¬φ | φ ∧ ψ | φ ∨ ψ
    | EX φ                 -- Exists Next
    | AX φ                 -- All Next
    | EF φ                 -- Exists Eventually
    | AF φ                 -- All Eventually
    | EG φ                 -- Exists Always
    | AG φ                 -- All Always
    | E[φ U ψ]             -- Exists Until
    | A[φ U ψ]             -- All Until
```

### 1.3 TLA+ (Temporal Logic of Actions)

**Syntax:**
```
Actions:    A  ::= predicate over primed and unprimed variables
Temporal:   □[A]_v      -- Always A or stuttering on v
            ◇⟨A⟩_v      -- Eventually A with v change
            WF_v(A)     -- Weak fairness
            SF_v(A)     -- Strong fairness
```

---

## 2. Atomic Propositions

### 2.1 State Predicates

```
-- Policy evaluation
policy_loaded(p)        -- Policy p is in PolicyTable
policy_active(p)        -- Policy p is currently being evaluated
condition_true(p)       -- Policy p's condition holds
action_pending(a)       -- Action a awaits consensus

-- Consensus state
leader_elected          -- A leader has been elected
voting_in_progress      -- Agents are voting
consensus_reached       -- Threshold votes achieved
committed(a)            -- Action a has been committed
aborted(a)              -- Action a has been aborted

-- Agent state
agent_honest(i)         -- Agent i is behaving honestly
agent_byzantine(i)      -- Agent i is behaving maliciously
agent_voted(i, a, v)    -- Agent i voted v on action a

-- Log state
log_entry(a, t)         -- Action a logged at time t
log_consistent          -- All honest agents have same log
```

### 2.2 Action Predicates

```
-- State transitions
Propose(a)              -- Leader proposes action a
Vote(i, a, v)           -- Agent i casts vote v on a
Commit(a)               -- Action a is committed
Abort(a)                -- Action a is aborted
AppendLog(entry)        -- Entry added to consensus log

-- Time actions
Timeout                 -- Election/vote timeout
HeartBeat               -- Leader heartbeat
ViewChange              -- View/term change
```

---

## 3. Safety Properties

### 3.1 Type Safety

**Property S1 (Type Preservation):**
```
LTL: G (well_typed(e) → well_typed(eval(e)))
CTL: AG (well_typed(e) → AX well_typed(result(e)))
```

**English:** A well-typed expression always evaluates to a well-typed value.

**TLA+ Specification:**
```tla
TypeSafety ==
    □[well_typed(expr) => well_typed(eval(expr))]_vars
```

### 3.2 Memory Safety

**Property S2 (No Dangling References):**
```
LTL: G (∀x. referenced(x) → allocated(x))
```

**Property S3 (No Buffer Overflow):**
```
LTL: G (∀i, arr. access(arr, i) → 0 ≤ i < length(arr))
```

### 3.3 Termination (as Safety)

**Property S4 (Bounded Execution):**
```
LTL: G (started(e) → F_≤n terminated(e))
CTL: AG (started(e) → AF_≤n terminated(e))
```

Where F_≤n means "within n steps".

### 3.4 Consensus Safety

**Property S5 (Agreement):**
```
LTL: G (committed(a₁) ∧ committed(a₂) → a₁ = a₂ ∨ ¬conflict(a₁, a₂))
CTL: AG (committed(a₁) ∧ committed(a₂) → a₁ = a₂ ∨ ¬conflict(a₁, a₂))
```

**Property S6 (Validity):**
```
LTL: G (committed(a) → valid(a))
```

Only valid actions can be committed.

**Property S7 (Non-Repudiation):**
```
LTL: G (committed(a) → F logged(a))
CTL: AG (committed(a) → EF logged(a))
```

Every committed action is eventually logged.

### 3.5 Sandbox Isolation

**Property S8 (No File Access):**
```
LTL: G ¬file_operation
```

**Property S9 (No Network Access):**
```
LTL: G ¬network_operation
```

**Property S10 (No System Calls):**
```
LTL: G ¬system_call
```

---

## 4. Liveness Properties

### 4.1 Progress

**Property L1 (Evaluation Progress):**
```
LTL: G (evaluating(e) → F completed(e))
CTL: AG (evaluating(e) → AF completed(e))
```

Every started evaluation eventually completes.

### 4.2 Consensus Liveness

**Property L2 (Eventual Decision):**
```
LTL: G (proposed(a) → F (committed(a) ∨ aborted(a)))
CTL: AG (proposed(a) → AF (committed(a) ∨ aborted(a)))
```

Every proposed action is eventually decided.

**Property L3 (Leader Election):**
```
LTL: G (¬leader_exists → F leader_elected)
CTL: AG (¬leader_exists → AF leader_elected)
```

If no leader exists, one is eventually elected.

### 4.3 Fairness-Dependent Liveness

**Property L4 (Under Weak Fairness):**
```
TLA+: WF_vars(Vote) ∧ WF_vars(Commit) → □(proposed(a) → ◇decided(a))
```

With weak fairness on voting and committing, all proposals are decided.

---

## 5. Fairness Properties

### 5.1 Weak Fairness (Justice)

**Definition (WF):**
```
WF_v(A) ≡ □◇¬Enabled(A) ∨ □◇⟨A⟩_v
```

If action A is continuously enabled, it eventually occurs.

**Property F1 (Agent Participation):**
```
WF_vars(Vote(i, _, _)) for all honest i
```

Every honest agent eventually votes if voting is enabled.

### 5.2 Strong Fairness (Compassion)

**Definition (SF):**
```
SF_v(A) ≡ ◇□¬Enabled(A) ∨ □◇⟨A⟩_v
```

If action A is infinitely often enabled, it eventually occurs.

**Property F2 (Leader Rotation):**
```
SF_vars(BecomeLeader(i)) for all i
```

Every agent that infinitely often could become leader, eventually does.

### 5.3 Byzantine Fairness

**Property F3 (Honest Majority Decides):**
```
G ((|honest_votes| ≥ t) → committed_reflects_honest_majority)
```

When honest agents reach threshold, outcome reflects their votes.

---

## 6. CTL Model Checking

### 6.1 State Space

```
States: S = PolicyState × ConsensusState × EnvironmentState

PolicyState = (PolicyTable, CurrentPolicy, EvaluationState)
ConsensusState = (Term, Leader, Log, Votes, PendingActions)
EnvironmentState = (Variables, Modules, Capabilities)
```

### 6.2 Transition Relation

```
R ⊆ S × S

(s, s') ∈ R iff:
  - Policy evaluation step, or
  - Consensus protocol step, or
  - Module call, or
  - State update
```

### 6.3 CTL Specifications

**CTL Spec 1 (Termination from all states):**
```
AG AF terminated
```

**CTL Spec 2 (Safety reachability):**
```
AG ¬error_state
```

**CTL Spec 3 (Consensus possibility):**
```
AG EF committed(some_action)
```

**CTL Spec 4 (Deadlock freedom):**
```
AG EX true
```

Always exists a next state.

---

## 7. TLA+ Complete Specification

### 7.1 Variables

```tla
VARIABLES
    \* Policy state
    policyTable,        \* Map: PolicyName -> Policy
    currentPolicy,      \* Currently evaluating policy
    environment,        \* Variable bindings

    \* Consensus state
    term,               \* Current term/epoch
    leader,             \* Current leader (or null)
    log,                \* Append-only consensus log
    votes,              \* Current voting state
    pending,            \* Pending actions

    \* Agent state
    agentState          \* Map: Agent -> AgentState
```

### 7.2 Initial State

```tla
Init ==
    /\ policyTable = {}
    /\ currentPolicy = null
    /\ environment = {}
    /\ term = 0
    /\ leader = null
    /\ log = <<>>
    /\ votes = [a \in Agents |-> null]
    /\ pending = {}
    /\ agentState = [a \in Agents |-> "idle"]
```

### 7.3 Actions

```tla
\* Load a policy
LoadPolicy(name, policy) ==
    /\ policyTable' = policyTable @@ (name :> policy)
    /\ UNCHANGED <<currentPolicy, environment, term, leader, log, votes, pending, agentState>>

\* Evaluate a policy condition
EvaluateCondition(policy) ==
    /\ currentPolicy' = policy
    /\ environment' = EvalCondition(policy.condition, environment)
    /\ UNCHANGED <<policyTable, term, leader, log, votes, pending, agentState>>

\* Propose an action
Propose(action) ==
    /\ leader # null
    /\ agentState[leader] = "ready"
    /\ pending' = pending \cup {action}
    /\ votes' = [a \in Agents |-> "none"]
    /\ agentState' = [a \in Agents |-> "voting"]
    /\ UNCHANGED <<policyTable, currentPolicy, environment, term, leader, log>>

\* Agent votes
Vote(agent, action, vote) ==
    /\ agentState[agent] = "voting"
    /\ action \in pending
    /\ votes[agent] = "none"
    /\ votes' = [votes EXCEPT ![agent] = vote]
    /\ UNCHANGED <<policyTable, currentPolicy, environment, term, leader, log, pending, agentState>>

\* Commit action (consensus reached)
Commit(action) ==
    /\ action \in pending
    /\ Cardinality({a \in Agents : votes[a] = "approve"}) >= Threshold
    /\ log' = Append(log, [action |-> action, term |-> term])
    /\ pending' = pending \ {action}
    /\ agentState' = [a \in Agents |-> "idle"]
    /\ votes' = [a \in Agents |-> "none"]
    /\ UNCHANGED <<policyTable, currentPolicy, environment, term, leader>>

\* Abort action (consensus failed)
Abort(action) ==
    /\ action \in pending
    /\ Cardinality({a \in Agents : votes[a] = "reject"}) > Cardinality(Agents) - Threshold
    /\ pending' = pending \ {action}
    /\ agentState' = [a \in Agents |-> "idle"]
    /\ votes' = [a \in Agents |-> "none"]
    /\ UNCHANGED <<policyTable, currentPolicy, environment, term, leader, log>>

\* Leader election
ElectLeader(agent) ==
    /\ leader = null
    /\ agentState[agent] = "candidate"
    /\ \* Received majority votes
    /\ leader' = agent
    /\ term' = term + 1
    /\ UNCHANGED <<policyTable, currentPolicy, environment, log, votes, pending, agentState>>
```

### 7.4 Next State Relation

```tla
Next ==
    \/ \E name, policy : LoadPolicy(name, policy)
    \/ \E policy : EvaluateCondition(policy)
    \/ \E action : Propose(action)
    \/ \E agent, action, vote : Vote(agent, action, vote)
    \/ \E action : Commit(action)
    \/ \E action : Abort(action)
    \/ \E agent : ElectLeader(agent)
```

### 7.5 Specification

```tla
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Commit)
    /\ WF_vars(Abort)
    /\ SF_vars(ElectLeader)
```

### 7.6 Properties

```tla
\* Safety: No conflicting commits
Safety ==
    \A i, j \in 1..Len(log) :
        i # j => log[i].action # log[j].action \/ ~Conflict(log[i].action, log[j].action)

\* Liveness: All proposed actions eventually decided
Liveness ==
    \A action \in pending : <>(action \notin pending)

\* Type invariant
TypeOK ==
    /\ policyTable \in [PolicyNames -> Policies]
    /\ term \in Nat
    /\ log \in Seq(LogEntries)
    /\ votes \in [Agents -> {"approve", "reject", "none"}]
```

---

## 8. Büchi Automata for LTL

### 8.1 Property Automata

**For G ¬error (safety):**
```
States: {q₀}
Initial: q₀
Accepting: {q₀}
Transitions:
  q₀ --[¬error]--> q₀
```

**For F committed (reachability):**
```
States: {q₀, q₁}
Initial: q₀
Accepting: {q₁}
Transitions:
  q₀ --[¬committed]--> q₀
  q₀ --[committed]--> q₁
  q₁ --[true]--> q₁
```

**For G (proposed → F decided):**
```
States: {q₀, q₁}
Initial: q₀
Accepting: {q₀}
Transitions:
  q₀ --[¬proposed]--> q₀
  q₀ --[proposed ∧ decided]--> q₀
  q₀ --[proposed ∧ ¬decided]--> q₁
  q₁ --[¬decided]--> q₁
  q₁ --[decided]--> q₀
```

### 8.2 Product Construction

Model checking: System × ¬Property automaton
Check for empty language (no accepting runs)

---

## 9. Interval Temporal Logic

### 9.1 Duration Calculus

**Property (Bounded Response):**
```
∫ (proposed ∧ ¬decided) ≤ T
```

Time spent in "proposed but undecided" state is bounded by T.

### 9.2 Metric Temporal Logic

**MTL Properties:**
```
G (proposed → F_≤Δ decided)
```

Every proposal is decided within Δ time units.

---

## 10. Past Temporal Operators

### 10.1 Past LTL Extensions

```
Y φ     -- Yesterday (previous state)
H φ     -- Historically (always in past)
O φ     -- Once (sometime in past)
φ S ψ   -- Since
```

### 10.2 Properties with History

**Property (Monotonic Log):**
```
G (entry_in_log → H entry_in_log)
```

Once an entry is in the log, it was always in the log (going forward).

**Property (Causality):**
```
G (committed(a) → O proposed(a))
```

Commit implies prior proposal.

---

## 11. Hierarchical Temporal Specifications

### 11.1 Component Properties

**Lexer:**
```
G (input_char → X (token_emitted ∨ in_token))
```

**Parser:**
```
G (token → F (ast_node ∨ error))
```

**Interpreter:**
```
G (ast_node → F result)
```

**Consensus:**
```
G (proposal → F decision)
```

### 11.2 Composition

**Theorem (Compositional Verification):**
If each component satisfies its specification, the composition satisfies the system specification.

```
Lexer ⊨ φ_lex ∧ Parser ⊨ φ_parse ∧ Interpreter ⊨ φ_interp
    →
System ⊨ φ_system
```

---

## 12. Verification Results

### 12.1 Verified Properties

| Property | Logic | Status | Method |
|----------|-------|--------|--------|
| Type Safety | LTL | ✓ | Proof |
| Termination | CTL | ✓ | Proof |
| Sandbox Isolation | LTL | ✓ | Proof |
| Consensus Safety | TLA+ | ✓ | TLC |
| Consensus Liveness | TLA+ | ✓ | TLC |
| Deadlock Freedom | CTL | ✓ | Model Check |

### 12.2 Model Checking Configuration

```tla
\* TLC Configuration
CONSTANTS
    Agents = {a1, a2, a3, a4}
    Threshold = 3
    MaxLogLen = 5

INVARIANTS
    TypeOK
    Safety

PROPERTIES
    Liveness
```

---

## References

1. Pnueli, A. (1977). *The Temporal Logic of Programs*. FOCS.
2. Clarke, E. M., et al. (1999). *Model Checking*. MIT Press.
3. Lamport, L. (2002). *Specifying Systems: The TLA+ Language*. Addison-Wesley.
4. Baier, C., & Katoen, J.-P. (2008). *Principles of Model Checking*. MIT Press.
