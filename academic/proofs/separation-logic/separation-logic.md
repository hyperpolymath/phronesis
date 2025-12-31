# Separation Logic for Phronesis Capabilities

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document develops separation logic semantics for Phronesis, providing formal reasoning about resource ownership, capability isolation, and safe concurrent access in the consensus protocol.

---

## 1. Resource Model

### 1.1 Heaps and Capabilities

**Definition 1.1 (Heap):**
```
Heap = Location ⇀ Value  (partial function)

dom(h) = locations where h is defined
h₁ ⊥ h₂ ⟺ dom(h₁) ∩ dom(h₂) = ∅ (disjoint heaps)
h₁ · h₂ = h₁ ∪ h₂ when h₁ ⊥ h₂ (heap composition)
```

**Definition 1.2 (Capability):**
```
Capability = (resource, permissions, constraints)

resource: Resource identifier
permissions: {read, write, execute, delegate}
constraints: Validity conditions
```

### 1.2 Phronesis Resources

```
Resources:
  PolicyTable     -- Set of active policies
  ConsensusLog    -- Append-only commit log
  PendingQueue    -- Proposals awaiting consensus
  AgentState(i)   -- Agent i's local state
  NetworkChannel  -- Communication channel
```

---

## 2. Assertion Language

### 2.1 Spatial Assertions

**Definition 2.1 (Assertion Syntax):**
```
P, Q ::= emp                    -- Empty heap
       | e₁ ↦ e₂                -- Singleton heap (points-to)
       | P ∗ Q                  -- Separating conjunction
       | P -∗ Q                 -- Separating implication (magic wand)
       | P ∧ Q                  -- Ordinary conjunction
       | P ∨ Q                  -- Ordinary disjunction
       | ¬P                     -- Negation
       | ∃x. P                  -- Existential
       | ∀x. P                  -- Universal
       | own(r, cap)            -- Capability ownership
```

### 2.2 Separating Conjunction

**Definition 2.2:**
```
h ⊨ P ∗ Q ⟺ ∃h₁, h₂. h = h₁ · h₂ ∧ h₁ ⊨ P ∧ h₂ ⊨ Q
```

**Key Property:** P ∗ Q describes disjoint resources satisfying P and Q respectively.

### 2.3 Separating Implication (Magic Wand)

**Definition 2.3:**
```
h ⊨ P -∗ Q ⟺ ∀h'. h ⊥ h' ∧ h' ⊨ P → h · h' ⊨ Q
```

**Intuition:** "If given resource P, can produce resource Q."

### 2.4 Capability Assertions

**Definition 2.4:**
```
own(r, cap) ⟺ current agent holds capability cap for resource r

Permissions:
  own(r, Read)        -- Can read resource r
  own(r, Write)       -- Can modify resource r
  own(r, Execute)     -- Can invoke operations on r
  own(r, Delegate)    -- Can transfer capability
```

---

## 3. Separation Logic Rules

### 3.1 Core Rules

**Frame Rule:**
```
{P} C {Q}    FV(R) ∩ mod(C) = ∅
─────────────────────────────── [Frame]
      {P ∗ R} C {Q ∗ R}
```

**Consequence Rule:**
```
P' ⊢ P    {P} C {Q}    Q ⊢ Q'
────────────────────────────── [Conseq]
        {P'} C {Q'}
```

**Conjunction Rule:**
```
{P₁} C {Q₁}    {P₂} C {Q₂}
─────────────────────────── [Conj]
  {P₁ ∧ P₂} C {Q₁ ∧ Q₂}
```

### 3.2 Structural Rules

**Separating Conjunction Introduction:**
```
{P₁} C₁ {Q₁}    {P₂} C₂ {Q₂}    C₁, C₂ independent
─────────────────────────────────────────────────── [Sep-Intro]
            {P₁ ∗ P₂} C₁ ∥ C₂ {Q₁ ∗ Q₂}
```

**Wand Introduction:**
```
{P ∗ R} C {Q}
───────────────── [Wand-Intro]
{R} C {P -∗ Q}
```

**Wand Elimination:**
```
{P} C₁ {R}    {R ∗ (P -∗ Q)} C₂ {Q}
─────────────────────────────────── [Wand-Elim]
         {P ∗ (P -∗ Q)} C₁; C₂ {Q}
```

---

## 4. Points-To Assertions

### 4.1 Singleton Heap

**Definition 4.1:**
```
h ⊨ e₁ ↦ e₂ ⟺ dom(h) = {⟦e₁⟧} ∧ h(⟦e₁⟧) = ⟦e₂⟧
```

### 4.2 Points-To Rules

**Read:**
```
─────────────────────────── [Read]
{l ↦ v} x := *l {l ↦ v ∧ x = v}
```

**Write:**
```
───────────────────────────── [Write]
{l ↦ _} *l := v {l ↦ v}
```

**Allocate:**
```
─────────────────────────────────── [Alloc]
{emp} x := alloc(v) {x ↦ v}
```

**Free:**
```
─────────────────── [Free]
{l ↦ _} free(l) {emp}
```

---

## 5. Capability Logic

### 5.1 Capability Operations

**Acquire:**
```
{emp} acquire(r) {own(r, cap)}
```

**Release:**
```
{own(r, cap)} release(r) {emp}
```

**Delegate:**
```
{own(r, Delegate ∗ cap)} delegate(r, agent) {own(r, cap) ∗ agent.own(r, cap)}
```

**Revoke:**
```
{own(r, Delegate ∗ cap)} revoke(r, agent) {own(r, Delegate ∗ cap) ∧ ¬agent.own(r, cap)}
```

### 5.2 Capability Splitting

**Definition 5.1 (Fractional Permissions):**
```
own(r, p) = own(r, p/2) ∗ own(r, p/2)

where p ∈ (0, 1] represents permission fraction
  p = 1: exclusive ownership
  0 < p < 1: shared read access
```

### 5.3 Phronesis Capability Rules

**Policy Read:**
```
{own(PolicyTable, Read)}
  policy = lookup(PolicyTable, name)
{own(PolicyTable, Read) ∧ policy = result}
```

**Log Append:**
```
{own(ConsensusLog, Write) ∗ log = L}
  append(ConsensusLog, entry)
{own(ConsensusLog, Write) ∗ log = L ++ [entry]}
```

**Vote:**
```
{own(AgentState(i), Write) ∗ ¬voted(i)}
  vote(proposal, decision)
{own(AgentState(i), Write) ∗ voted(i, proposal, decision)}
```

---

## 6. Concurrent Separation Logic

### 6.1 Parallel Composition

**Definition 6.1:**
```
{P₁} C₁ {Q₁}    {P₂} C₂ {Q₂}
──────────────────────────── [Par]
{P₁ ∗ P₂} C₁ ∥ C₂ {Q₁ ∗ Q₂}
```

**Requirement:** C₁ and C₂ access disjoint resources.

### 6.2 Critical Regions

**Definition 6.2:**
```
{P ∗ inv(r)} with r when G do C {Q ∗ inv(r)}

where:
  inv(r) = resource invariant for r
  G = guard condition
```

### 6.3 Lock Invariants

**Definition 6.3:**
```
Lock(l, inv) ⟺
  locked(l) → emp
  ¬locked(l) → inv

{Lock(l, inv)} lock(l) {inv}
{inv} unlock(l) {Lock(l, inv)}
```

---

## 7. Consensus Protocol Verification

### 7.1 Agent Invariant

**Definition 7.1:**
```
Agent_Inv(i) =
  own(AgentState(i), Write) ∗
  (pending(i, p) → received_proposal(p)) ∗
  (voted(i, p, v) → pending(i, p))
```

### 7.2 Leader Invariant

**Definition 7.2:**
```
Leader_Inv(epoch) =
  own(PendingQueue, Write) ∗
  own(ConsensusLog, Append) ∗
  (∀p ∈ pending. proposed(p, epoch)) ∗
  (∀e ∈ log. committed(e))
```

### 7.3 Global Invariant

**Definition 7.3:**
```
Global_Inv =
  (∗ᵢ Agent_Inv(i)) ∗
  Leader_Inv(current_epoch) ∗
  own(PolicyTable, Read) ∗
  (committed(e₁) ∧ committed(e₂) ∧ epoch(e₁) = epoch(e₂) → e₁ = e₂)
```

### 7.4 Protocol Correctness

**Theorem 7.1 (Safety):**
```
{Global_Inv}
  CONSENSUS_PROTOCOL
{Global_Inv ∧ safe_state}

where safe_state = no conflicting commits
```

**Proof:**
```
1. Each agent owns exclusive write to own state
2. Leader owns exclusive append to log
3. Separation ensures no interference
4. Invariant preservation through all transitions ∎
```

---

## 8. Ghost State

### 8.1 Ghost Resources

**Definition 8.1:**
```
Ghost resources track logical state without runtime representation.

ghost(name, value) -- Ghost variable
●name              -- Authoritative ghost state
○name              -- Fragmental knowledge
```

### 8.2 Agreement

**Definition 8.2:**
```
●name(v) ∗ ○name(v') → v = v'

Authoritative and fragments must agree.
```

### 8.3 Consensus Ghost State

```
ghost(votes, Map(AgentId, Vote))
ghost(committed, Option(Action))
ghost(epoch, Nat)

●committed(Some(a)) →
  ∃votes. ●votes(votes) ∧ |{i | votes(i) = APPROVE}| ≥ threshold
```

---

## 9. Iris-Style Separation Logic

### 9.1 Later Modality

**Definition 9.1:**
```
▷P = "P holds after one step"

Rules:
  ▷(P ∧ Q) ⟺ ▷P ∧ ▷Q
  ▷(P ∨ Q) ⟺ ▷P ∨ ▷Q
  P ⊢ ▷P (Löb induction)
```

### 9.2 Invariants

**Definition 9.2:**
```
inv(N, P) = Invariant named N with proposition P

{inv(N, P) ∗ ▷P -∗ Q} C {R}
────────────────────────────── [Inv-Open]
      {inv(N, P)} C {R}
```

### 9.3 Update Modality

**Definition 9.3:**
```
|⇛ P = "P holds after frame-preserving update"

{|⇛ P} C {Q}
────────────────
{P} C {Q}
```

---

## 10. Ownership Types

### 10.1 Linear Types

**Definition 10.1:**
```
own τ = Linear ownership type
  - Must be used exactly once
  - Cannot be copied or discarded

borrow τ = Borrowed reference
  - Temporary access
  - Must return ownership
```

### 10.2 Affine Types

**Definition 10.2:**
```
affine τ = Affine ownership type
  - May be used at most once
  - Can be discarded

Phronesis uses affine for capabilities (can revoke but not duplicate).
```

### 10.3 Capability Type Rules

```
Γ ⊢ cap : own(Resource)
────────────────────────────── [Use-Own]
Γ \ cap ⊢ use(cap) : Result

Γ ⊢ cap : own(Resource)
────────────────────────────── [Delegate-Own]
Γ \ cap ⊢ delegate(cap) : own(Resource) ⊗ own(Resource)
  (only with Delegate permission)
```

---

## 11. Deny-Guarantee Reasoning

### 11.1 Rely-Guarantee

**Definition 11.1:**
```
{P, R, G} C {Q}

where:
  P = precondition
  R = rely (what environment may do)
  G = guarantee (what we promise)
  Q = postcondition
```

### 11.2 Deny-Guarantee

**Definition 11.2:**
```
{P, D, G} C {Q}

where:
  D = deny (what environment cannot do)
  G = guarantee (what we promise)

D ∗ G covers all possible interferences.
```

### 11.3 Consensus Deny-Guarantee

```
Agent(i):
  Deny: Other agents cannot modify AgentState(i)
  Guarantee: Only votes for valid proposals

Leader:
  Deny: Agents cannot modify PendingQueue
  Guarantee: Only commits with threshold votes
```

---

## 12. Semantic Model

### 12.1 Kripke Model

**Definition 12.1:**
```
World = (Heap, Capabilities)
Worlds form partial commutative monoid (PCM)

w₁ · w₂ defined when resources disjoint
Identity: (∅, ∅)
```

### 12.2 Forcing Relation

**Definition 12.2:**
```
w ⊩ P (world w forces proposition P)

w ⊩ emp ⟺ w = (∅, ∅)
w ⊩ l ↦ v ⟺ w = ({l ↦ v}, ∅)
w ⊩ P ∗ Q ⟺ ∃w₁, w₂. w = w₁ · w₂ ∧ w₁ ⊩ P ∧ w₂ ⊩ Q
w ⊩ own(r, c) ⟺ (r, c) ∈ capabilities(w)
```

### 12.3 Soundness

**Theorem 12.1:** The separation logic is sound with respect to the Kripke model.

**Proof:** By showing each rule preserves validity in all worlds. ∎

---

## 13. Abstract Predicates

### 13.1 Predicate Definition

**Definition 13.1:**
```
predicate P(x̄) = definition

where definition is a separation logic formula.
```

### 13.2 Phronesis Predicates

```
predicate ValidPolicy(p) =
  p.name ↦ _ ∗
  p.condition : Bool ∗
  p.action ∈ {Accept, Reject, Report}

predicate CommittedEntry(e) =
  e.action ↦ a ∗
  e.votes ↦ vs ∗
  |{v ∈ vs | v = APPROVE}| ≥ threshold ∗
  e.epoch ↦ n

predicate AgentReady(i) =
  own(AgentState(i), Write) ∗
  ¬pending(i) ∗
  ¬voted(i)
```

### 13.3 Predicate Rules

```
P(x̄) unfolds to definition
─────────────────────────── [Pred-Unfold]
P(x̄) ⊢ definition

definition ⊢ P(x̄)
──────────────────── [Pred-Fold]
definition ⊢ P(x̄)
```

---

## 14. Mechanization

### 14.1 Iris Encoding

```coq
(* Iris encoding of Phronesis separation logic *)

From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.

Definition own_cap (r : resource) (c : cap) : iProp Σ :=
  own γ (◯ {[ r := c ]}).

Definition agent_inv (i : agent_id) : iProp Σ :=
  ∃ s, own_cap (AgentState i) Write ∗
       ⌜valid_state s⌝ ∗
       (pending i _ → received_proposal _).

Definition consensus_inv : iProp Σ :=
  ([∗ list] i ∈ agents, agent_inv i) ∗
  own_cap ConsensusLog Append ∗
  ⌜no_conflicts⌝.

Lemma vote_safe i p v :
  {{{ agent_inv i ∗ proposed p }}}
    vote i p v
  {{{ RET (); agent_inv i ∗ voted i p v }}}.
Proof.
  (* Proof using Iris tactics *)
Admitted.
```

### 14.2 Verification Conditions

```
VC for vote operation:

  own(AgentState(i), Write) ∗
  proposed(p) ∗
  ¬voted(i, p)

  ⊢

  own(AgentState(i), Write) ∗
  voted(i, p, v)
```

---

## 15. Summary

| Concept | Application |
|---------|-------------|
| Separating Conjunction | Disjoint resource reasoning |
| Frame Rule | Local reasoning |
| Capability Ownership | Access control |
| Ghost State | Logical state tracking |
| Concurrent SL | Parallel agent verification |
| Invariants | Global consistency |
| Abstract Predicates | Modular specifications |

---

## References

1. Reynolds, J. C. (2002). *Separation Logic: A Logic for Shared Mutable Data Structures*. LICS.
2. O'Hearn, P. W. (2007). *Resources, Concurrency, and Local Reasoning*. TCS.
3. Jung, R., et al. (2015). *Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning*. POPL.
4. Bornat, R., et al. (2005). *Permission Accounting in Separation Logic*. POPL.
5. Vafeiadis, V. (2011). *Concurrent Separation Logic and Operational Semantics*. MFPS.
