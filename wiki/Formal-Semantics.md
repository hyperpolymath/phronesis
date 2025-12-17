# Formal Semantics

Mathematical specification of Phronesis operational semantics.

---

## Overview

Phronesis uses small-step operational semantics to define program execution. This provides:

1. **Precision**: Unambiguous execution behavior
2. **Verifiability**: Formal proofs of properties
3. **Determinism**: Same input always produces same output

---

## State Model

### Configuration

Execution state is a 5-tuple:

```
σ = (Π, Λ, Γ, Δ, Α)
```

Where:
- **Π** (Pi): PolicyTable - map from names to policies
- **Λ** (Lambda): ConsensusLog - append-only sequence of entries
- **Γ** (Gamma): Environment - map from names to values
- **Δ** (Delta): PendingActions - set of actions awaiting consensus
- **Α** (Alpha): Agents - set of participating agents

### State Notation

```
Π = {p₁ ↦ def₁, p₂ ↦ def₂, ...}
Λ = [(a₁, r₁, v₁), (a₂, r₂, v₂), ...]
Γ = {x₁ ↦ v₁, x₂ ↦ v₂, ...}
Δ = {a₁, a₂, ...}
Α = {α₁, α₂, ...}
```

---

## Evaluation Judgments

### Expression Evaluation

```
Γ ⊢ e ⇓ v
```

"In environment Γ, expression e evaluates to value v"

### State Transition

```
σ →ₚ σ'
```

"State σ transitions to state σ' by policy p"

### Action Execution

```
σ, a ⟹ σ', r
```

"In state σ, action a executes producing state σ' and result r"

---

## Evaluation Rules

### Rule 1: POLICY-MATCH

When a route event occurs, find the highest priority matching policy:

```
                route ∈ Routes
                P = {p ∈ Π | Γ[route ↦ route] ⊢ p.condition ⇓ true}
                p_max = argmax_{p ∈ P}(p.priority)
────────────────────────────────────────────────────────────────── [POLICY-MATCH]
(Π, Λ, Γ, Δ, Α), route → (Π, Λ, Γ, Δ ∪ {p_max.action}, Α)
```

### Rule 2: ACTION-EXECUTE

Execute a pending action with consensus:

```
                a ∈ Δ
                votes = consensus(a, Α)
                |{v ∈ votes | v = approve}| / |Α| ≥ threshold
                result = exec(a)
────────────────────────────────────────────────────────────────── [ACTION-EXECUTE]
(Π, Λ, Γ, Δ, Α) → (Π, Λ ++ [(a, result, votes)], Γ, Δ \ {a}, Α)
```

### Rule 3: COND-TRUE

Evaluate conditional when condition is true:

```
                Γ ⊢ e_cond ⇓ true
                Γ ⊢ e_then ⇓ v
────────────────────────────────────────────────────── [COND-TRUE]
Γ ⊢ IF e_cond THEN e_then ELSE e_else ⇓ v
```

### Rule 4: COND-FALSE

Evaluate conditional when condition is false:

```
                Γ ⊢ e_cond ⇓ false
                Γ ⊢ e_else ⇓ v
────────────────────────────────────────────────────── [COND-FALSE]
Γ ⊢ IF e_cond THEN e_then ELSE e_else ⇓ v
```

### Rule 5: MODULE-CALL

Call a registered module function:

```
                M ∈ RegisteredModules
                has_capability(Γ, M.required_cap)
                Γ ⊢ e₁ ⇓ v₁, ..., Γ ⊢ eₙ ⇓ vₙ
                result = M.call(v₁, ..., vₙ)
────────────────────────────────────────────────────── [MODULE-CALL]
Γ ⊢ M.f(e₁, ..., eₙ) ⇓ result
```

---

## Expression Evaluation Rules

### Literals

```
────────────── [E-INT]
Γ ⊢ n ⇓ n

────────────── [E-BOOL]
Γ ⊢ b ⇓ b

────────────── [E-STRING]
Γ ⊢ s ⇓ s
```

### Variables

```
        x ∈ dom(Γ)
────────────────────── [E-VAR]
    Γ ⊢ x ⇓ Γ(x)
```

### Arithmetic

```
        Γ ⊢ e₁ ⇓ n₁    Γ ⊢ e₂ ⇓ n₂
────────────────────────────────────── [E-ADD]
        Γ ⊢ e₁ + e₂ ⇓ n₁ + n₂

        Γ ⊢ e₁ ⇓ n₁    Γ ⊢ e₂ ⇓ n₂
────────────────────────────────────── [E-MUL]
        Γ ⊢ e₁ * e₂ ⇓ n₁ × n₂
```

### Comparison

```
        Γ ⊢ e₁ ⇓ v₁    Γ ⊢ e₂ ⇓ v₂
────────────────────────────────────── [E-EQ]
        Γ ⊢ e₁ == e₂ ⇓ v₁ = v₂

        Γ ⊢ e₁ ⇓ n₁    Γ ⊢ e₂ ⇓ n₂
────────────────────────────────────── [E-LT]
        Γ ⊢ e₁ < e₂ ⇓ n₁ < n₂
```

### Logical

```
        Γ ⊢ e₁ ⇓ true    Γ ⊢ e₂ ⇓ b
────────────────────────────────────────── [E-AND-TRUE]
        Γ ⊢ e₁ AND e₂ ⇓ b

        Γ ⊢ e₁ ⇓ false
────────────────────────────────────────── [E-AND-FALSE]
        Γ ⊢ e₁ AND e₂ ⇓ false

        Γ ⊢ e₁ ⇓ false    Γ ⊢ e₂ ⇓ b
────────────────────────────────────────── [E-OR-FALSE]
        Γ ⊢ e₁ OR e₂ ⇓ b

        Γ ⊢ e₁ ⇓ true
────────────────────────────────────────── [E-OR-TRUE]
        Γ ⊢ e₁ OR e₂ ⇓ true

        Γ ⊢ e ⇓ b
────────────────────────────────────────── [E-NOT]
        Γ ⊢ NOT e ⇓ ¬b
```

### Membership

```
        Γ ⊢ e₁ ⇓ v    Γ ⊢ e₂ ⇓ [v₁, ..., vₙ]    v ∈ {v₁, ..., vₙ}
──────────────────────────────────────────────────────────────────── [E-IN-TRUE]
        Γ ⊢ e₁ IN e₂ ⇓ true

        Γ ⊢ e₁ ⇓ v    Γ ⊢ e₂ ⇓ [v₁, ..., vₙ]    v ∉ {v₁, ..., vₙ}
──────────────────────────────────────────────────────────────────── [E-IN-FALSE]
        Γ ⊢ e₁ IN e₂ ⇓ false
```

### Field Access

```
        Γ ⊢ e ⇓ {f₁: v₁, ..., fₙ: vₙ}    f ∈ {f₁, ..., fₙ}
──────────────────────────────────────────────────────────── [E-FIELD]
        Γ ⊢ e.f ⇓ vᵢ where fᵢ = f
```

---

## Action Semantics

### ACCEPT

```
        Γ ⊢ e ⇓ v
────────────────────────────── [A-ACCEPT]
σ, ACCEPT(e) ⟹ σ, Accept(v)
```

### REJECT

```
        Γ ⊢ e ⇓ v
────────────────────────────── [A-REJECT]
σ, REJECT(e) ⟹ σ, Reject(v)
```

### REPORT

```
        Γ ⊢ e ⇓ v
        Λ' = Λ ++ [(REPORT, v, ∅)]
────────────────────────────────────────── [A-REPORT]
(Π, Λ, Γ, Δ, Α), REPORT(e) ⟹ (Π, Λ', Γ, Δ, Α), Report(v)
```

---

## Type System

### Type Syntax

```
τ ::= Int | Float | String | Bool | IP | DateTime
    | List τ | Record {f₁: τ₁, ..., fₙ: τₙ} | Null
```

### Typing Rules

```
        n is integer literal
────────────────────────────── [T-INT]
        Γ ⊢ n : Int

        Γ ⊢ e₁ : Int    Γ ⊢ e₂ : Int
────────────────────────────────────── [T-ADD]
        Γ ⊢ e₁ + e₂ : Int

        Γ ⊢ e₁ : τ    Γ ⊢ e₂ : τ
────────────────────────────────────── [T-EQ]
        Γ ⊢ e₁ == e₂ : Bool

        Γ ⊢ e₁ : Bool    Γ ⊢ e₂ : Bool
────────────────────────────────────────── [T-AND]
        Γ ⊢ e₁ AND e₂ : Bool
```

---

## Theorems

### Theorem 1: Termination

**Statement**: All Phronesis programs terminate.

**Proof**: By structural induction on the AST.

*Base cases*:
- Literals: O(1) evaluation
- Variables: O(1) lookup

*Inductive cases*:
- Binary ops: subexpressions terminate (IH), operation is O(1)
- Conditionals: condition terminates (IH), one branch terminates (IH)
- Module calls: modules are finite, terminating functions

No constructs allow unbounded iteration or recursion. ∎

### Theorem 2: Determinism

**Statement**: For all σ, e: if Γ ⊢ e ⇓ v₁ and Γ ⊢ e ⇓ v₂, then v₁ = v₂.

**Proof**: By induction on the derivation.

Each evaluation rule has non-overlapping premises and produces a unique value. ∎

### Theorem 3: Progress

**Statement**: For well-typed e, either e is a value or ∃v: Γ ⊢ e ⇓ v.

**Proof**: By induction on typing derivation.

Each typing rule corresponds to an evaluation rule that can make progress. ∎

### Theorem 4: Preservation

**Statement**: If Γ ⊢ e : τ and Γ ⊢ e ⇓ v, then v has type τ.

**Proof**: By induction on the evaluation derivation, using the typing rules. ∎

---

## Consensus Protocol Semantics

### Raft State Machine

```
State = (currentTerm, votedFor, log, commitIndex, state)

state ∈ {Follower, Candidate, Leader}
```

### Leader Election

```
        state = Follower
        timeout elapsed
        term' = currentTerm + 1
────────────────────────────────────────── [BECOME-CANDIDATE]
(term, votedFor, log, ci, Follower) →
(term', self, log, ci, Candidate)

        state = Candidate
        received majority votes
────────────────────────────────────────── [BECOME-LEADER]
(term, votedFor, log, ci, Candidate) →
(term, votedFor, log, ci, Leader)
```

### Log Replication

```
        state = Leader
        command c received
        log' = log ++ [(term, c)]
────────────────────────────────────────── [APPEND-ENTRY]
(term, vf, log, ci, Leader) →
(term, vf, log', ci, Leader)

        majority have log[i]
        i > commitIndex
────────────────────────────────────────── [COMMIT]
(term, vf, log, ci, Leader) →
(term, vf, log, i, Leader)
```

---

## Safety Properties

### Safety Invariants

1. **Election Safety**: At most one leader per term
2. **Log Matching**: If two logs have same index and term, they're identical
3. **Leader Completeness**: Committed entries appear in all future leaders' logs
4. **State Machine Safety**: All nodes apply same commands in same order

### Formal Statements

```
∀ t ∈ Terms: |{n ∈ Nodes | state(n) = Leader ∧ term(n) = t}| ≤ 1

∀ n₁, n₂ ∈ Nodes, i ∈ ℕ:
  log(n₁)[i].term = log(n₂)[i].term →
  log(n₁)[1..i] = log(n₂)[1..i]

∀ t₁, t₂ ∈ Terms, e ∈ Entries:
  committed(e, t₁) ∧ t₂ > t₁ →
  e ∈ log(leader(t₂))
```

---

## See Also

- [Reference-Grammar](Reference-Grammar.md) - Formal grammar
- [Architecture-Interpreter](Architecture-Interpreter.md) - Implementation
- [Testing](Testing.md) - Verification via testing
- [docs/safety_proofs.md](../docs/safety_proofs.md) - Safety proofs document
