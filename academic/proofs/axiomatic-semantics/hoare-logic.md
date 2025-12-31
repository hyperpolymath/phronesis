# Axiomatic Semantics for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides axiomatic (Hoare logic) semantics for Phronesis, enabling formal reasoning about program correctness through preconditions and postconditions.

---

## 1. Hoare Triples

### 1.1 Syntax

**Definition 1.1 (Hoare Triple):**
```
{P} S {Q}

where:
  P = precondition (assertion before execution)
  S = statement/expression
  Q = postcondition (assertion after execution)
```

### 1.2 Partial vs Total Correctness

**Partial Correctness:** {P} S {Q}
- If P holds and S terminates, then Q holds

**Total Correctness:** [P] S [Q]
- If P holds, then S terminates and Q holds

**For Phronesis:** Partial = Total (all programs terminate)

### 1.3 Assertion Language

```
φ ::= true | false              -- Boolean constants
    | e₁ = e₂                   -- Equality
    | e₁ < e₂                   -- Comparison
    | φ₁ ∧ φ₂                   -- Conjunction
    | φ₁ ∨ φ₂                   -- Disjunction
    | ¬φ                        -- Negation
    | φ₁ → φ₂                   -- Implication
    | ∀x:τ. φ                   -- Universal quantification
    | ∃x:τ. φ                   -- Existential quantification
```

---

## 2. Axioms and Rules

### 2.1 Skip/Value Axiom

```
─────────────── [Skip]
{P} skip {P}

─────────────────────── [Value]
{P[e/result]} e {P}
```

### 2.2 Assignment Axiom

For constant binding:
```
───────────────────────────── [Const]
{P[e/x]} CONST x = e {P}
```

### 2.3 Sequence Rule

```
{P} S₁ {Q}    {Q} S₂ {R}
─────────────────────────── [Seq]
     {P} S₁; S₂ {R}
```

### 2.4 Conditional Rule

```
{P ∧ b} S₁ {Q}    {P ∧ ¬b} S₂ {Q}
─────────────────────────────────── [If]
   {P} IF b THEN S₁ ELSE S₂ {Q}
```

### 2.5 Consequence Rule

```
P' → P    {P} S {Q}    Q → Q'
───────────────────────────────── [Conseq]
        {P'} S {Q'}
```

### 2.6 Conjunction Rule

```
{P₁} S {Q₁}    {P₂} S {Q₂}
────────────────────────────── [Conj]
   {P₁ ∧ P₂} S {Q₁ ∧ Q₂}
```

### 2.7 Disjunction Rule

```
{P₁} S {Q₁}    {P₂} S {Q₂}
────────────────────────────── [Disj]
   {P₁ ∨ P₂} S {Q₁ ∨ Q₂}
```

---

## 3. Expression Rules

### 3.1 Arithmetic Expressions

```
───────────────────────────────────────── [Add]
{P[(x + y)/result]} x + y {P}

───────────────────────────────────────── [Mul]
{P[(x * y)/result]} x * y {P}
```

### 3.2 Boolean Expressions

```
───────────────────────────────────────── [And]
{P[(x ∧ y)/result]} x AND y {P}

───────────────────────────────────────── [Or]
{P[(x ∨ y)/result]} x OR y {P}

───────────────────────────────────────── [Not]
{P[(¬x)/result]} NOT x {P}
```

### 3.3 Comparison Expressions

```
───────────────────────────────────────── [Eq]
{P[(x = y)/result]} x == y {P}

───────────────────────────────────────── [Lt]
{P[(x < y)/result]} x < y {P}
```

### 3.4 Field Access

```
────────────────────────────────────────────── [Field]
{P[r.f/result]} r.f {P}

where r : Record{..., f:τ, ...}
```

### 3.5 List Membership

```
────────────────────────────────────────────── [In]
{P[(x ∈ L)/result]} x IN L {P}
```

---

## 4. Policy Rules

### 4.1 Policy Evaluation

```
{P ∧ cond} action {Q}
{P ∧ ¬cond} else_action {Q}
──────────────────────────────────────────────── [Policy]
{P} POLICY name: cond THEN action ELSE else_action {Q}
```

### 4.2 Accept Action

```
{P} ACCEPT(msg) {result = Accept(msg) ∧ P}
```

### 4.3 Reject Action

```
{P} REJECT(msg) {result = Reject(msg) ∧ P}
```

### 4.4 Report Action

```
{P ∧ log = L} REPORT(msg) {log = L ++ [msg] ∧ P}
```

---

## 5. Weakest Precondition

### 5.1 Definition

**Definition 5.1 (Weakest Precondition):**
```
wp(S, Q) = weakest P such that {P} S {Q}
```

### 5.2 Weakest Precondition Calculus

```
wp(skip, Q) = Q

wp(CONST x = e, Q) = Q[e/x]

wp(S₁; S₂, Q) = wp(S₁, wp(S₂, Q))

wp(IF b THEN S₁ ELSE S₂, Q) = (b → wp(S₁, Q)) ∧ (¬b → wp(S₂, Q))
                             = (b ∧ wp(S₁, Q)) ∨ (¬b ∧ wp(S₂, Q))

wp(e₁ + e₂, Q) = Q[(e₁ + e₂)/result]

wp(x == y, Q) = Q[(x = y)/result]

wp(ACCEPT(msg), Q) = Q[Accept(msg)/result]
```

### 5.3 Healthiness Conditions

**Theorem 5.1:** wp satisfies:
1. **Monotonicity:** Q → Q' implies wp(S, Q) → wp(S, Q')
2. **Conjunctivity:** wp(S, Q₁ ∧ Q₂) = wp(S, Q₁) ∧ wp(S, Q₂)
3. **Excluded Miracle:** wp(S, false) = false (for terminating S)

---

## 6. Strongest Postcondition

### 6.1 Definition

**Definition 6.1:**
```
sp(P, S) = strongest Q such that {P} S {Q}
```

### 6.2 Strongest Postcondition Calculus

```
sp(P, skip) = P

sp(P, CONST x = e) = ∃x₀. P[x₀/x] ∧ x = e[x₀/x]

sp(P, S₁; S₂) = sp(sp(P, S₁), S₂)

sp(P, IF b THEN S₁ ELSE S₂) = sp(P ∧ b, S₁) ∨ sp(P ∧ ¬b, S₂)
```

### 6.3 Duality

**Theorem 6.1:**
```
P → wp(S, Q)  ⟺  sp(P, S) → Q
```

---

## 7. Verification Conditions

### 7.1 Generation

**Definition 7.1 (Verification Condition):**
Given {P} S {Q}, the VC is:
```
VC(P, S, Q) = P → wp(S, Q)
```

### 7.2 Example: Policy Verification

```
Policy:
  POLICY reject_bogons:
    route.prefix IN bogon_list
    THEN REJECT("bogon detected")
    PRIORITY: 100

Precondition: route.prefix ∈ bogon_list
Postcondition: result = Reject("bogon detected")

VC:
  route.prefix ∈ bogon_list
  → wp(REJECT("bogon detected"), result = Reject("bogon detected"))
  = route.prefix ∈ bogon_list
  → result = Reject("bogon detected")
  = true  ✓
```

### 7.3 Automated Verification

```
Algorithm VerifyPolicy(policy):
  P = policy.condition
  action = policy.thenAction
  Q = expected_postcondition(action)

  vc = P → wp(action, Q)
  return SMT_check(vc)
```

---

## 8. Program Logic for Consensus

### 8.1 Distributed Hoare Logic

**Notation:**
```
{P}ᵢ Sᵢ {Q}ᵢ

Agent i: if Pᵢ holds locally, after Sᵢ, Qᵢ holds
```

### 8.2 Consensus Rules

**Vote Rule:**
```
{proposed(a) ∧ valid(a)}ᵢ Vote(APPROVE) {voted(i, a, APPROVE)}ᵢ
{proposed(a) ∧ ¬valid(a)}ᵢ Vote(REJECT) {voted(i, a, REJECT)}ᵢ
```

**Commit Rule:**
```
{|{i | voted(i, a, APPROVE)}| ≥ t} Commit(a) {committed(a) ∧ logged(a)}
```

### 8.3 Agreement Proof

**Theorem 8.1:**
```
{proposed(a₁) ∧ proposed(a₂)}
Protocol
{committed(a₁) ∧ committed(a₂) → a₁ = a₂}
```

**Proof:**
```
Assume committed(a₁) ∧ committed(a₂).
By Commit rule: |{i | voted(i, a₁, APPROVE)}| ≥ t
               |{i | voted(i, a₂, APPROVE)}| ≥ t

Since t > N/2: These sets overlap.
Some honest agent voted APPROVE for both.
Contradiction with single-vote invariant.
Therefore a₁ = a₂. ∎
```

---

## 9. Invariants

### 9.1 Type Invariants

```
Inv_Int(x) ≡ x ∈ ℤ
Inv_Bool(x) ≡ x ∈ {true, false}
Inv_List(τ)(L) ≡ ∀i. L[i] : τ
Inv_IP(x) ≡ 0 ≤ x.addr < 2³² ∧ 0 ≤ x.prefix ≤ 32
```

### 9.2 State Invariants

```
Inv_State ≡
  ∧ ∀p ∈ PolicyTable. valid_policy(p)
  ∧ ∀e ∈ ConsensusLog. valid_entry(e)
  ∧ ConsensusLog is append-only
  ∧ |pending| ≤ max_pending
```

### 9.3 Consensus Invariants

```
Inv_Consensus ≡
  ∧ |{i | state(i) = Leader ∧ term(i) = t}| ≤ 1  (Election Safety)
  ∧ ∀i,j,k. log(i)[k].term = log(j)[k].term → log(i)[1..k] = log(j)[1..k]
  ∧ ∀e ∈ committed. ∀t' > e.term. e ∈ log(leader(t'))
```

---

## 10. Refinement

### 10.1 Refinement Relation

**Definition 10.1:**
S₁ ⊑ S₂ (S₂ refines S₁) iff:
```
∀P, Q. {P} S₁ {Q} → {P} S₂ {Q}
```

### 10.2 Refinement Calculus

```
skip ⊑ S                      (for any terminating S)
S ⊑ S                         (reflexivity)
S₁ ⊑ S₂ ∧ S₂ ⊑ S₃ → S₁ ⊑ S₃  (transitivity)
```

### 10.3 Implementation Refinement

```
Spec:    {valid(route)} evaluate_policy {result ∈ {Accept, Reject}}
Impl:    actual Phronesis implementation

To verify: Impl ⊑ Spec
```

---

## 11. Separation Logic (for Capabilities)

### 11.1 Separating Conjunction

```
P * Q = P and Q hold for disjoint resources
```

### 11.2 Capability Assertions

```
has_cap(c) = agent holds capability c
c ↦ v = capability c points to value v
```

### 11.3 Frame Rule

```
{P} S {Q}    FV(R) ∩ mod(S) = ∅
──────────────────────────────── [Frame]
      {P * R} S {Q * R}
```

### 11.4 Capability Rules

```
{has_cap(c)} use(c) {has_cap(c)}           (capability preserved)
{has_cap(c)} revoke(c) {¬has_cap(c)}       (capability revoked)
{has_cap(c) * has_cap(c')} S {Q}           (no capability duplication without *)
```

---

## 12. Mechanization

### 12.1 Verification Condition Generator

```
vcgen : Stmt × Postcond → Precond

vcgen(skip, Q) = Q
vcgen(x := e, Q) = Q[e/x]
vcgen(S₁; S₂, Q) = vcgen(S₁, vcgen(S₂, Q))
vcgen(if b then S₁ else S₂, Q) =
  (b → vcgen(S₁, Q)) ∧ (¬b → vcgen(S₂, Q))
```

### 12.2 SMT Encoding

```
; SMT-LIB format for VC checking
(declare-sort Value)
(declare-fun route_prefix () Value)
(declare-fun bogon_list () (List Value))
(declare-fun member (Value (List Value)) Bool)

(assert (=> (member route_prefix bogon_list)
            (= result (Reject "bogon"))))

(check-sat)  ; Should return UNSAT (VC is valid)
```

---

## 13. Summary

| Construct | Weakest Precondition |
|-----------|---------------------|
| skip | Q |
| x := e | Q[e/x] |
| S₁; S₂ | wp(S₁, wp(S₂, Q)) |
| if b then S₁ else S₂ | (b → wp(S₁,Q)) ∧ (¬b → wp(S₂,Q)) |
| ACCEPT(m) | Q[Accept(m)/result] |
| REJECT(m) | Q[Reject(m)/result] |

---

## References

1. Hoare, C. A. R. (1969). *An Axiomatic Basis for Computer Programming*. CACM.
2. Dijkstra, E. W. (1976). *A Discipline of Programming*. Prentice-Hall.
3. Reynolds, J. C. (2002). *Separation Logic: A Logic for Shared Mutable Data Structures*.
4. Apt, K. R., et al. (2009). *Verification of Sequential and Concurrent Programs*. Springer.
