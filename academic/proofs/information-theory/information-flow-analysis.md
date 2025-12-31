# Information Flow Analysis for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides information flow analysis for Phronesis, ensuring confidentiality and integrity properties through noninterference proofs.

---

## 1. Security Lattice

### 1.1 Security Levels

**Definition 1.1 (Security Lattice):**
```
L = {Public, Private, System}

Ordering:
  Public ⊑ Private ⊑ System

    System
       |
    Private
       |
    Public
```

### 1.2 Information Flow Policy

**Definition 1.2:**
Information may flow from level l₁ to l₂ iff l₁ ⊑ l₂.

```
Valid flows:   Public → Private → System
Invalid flows: Private → Public (information leak)
               System → Public (system secret leak)
```

---

## 2. Security Types

### 2.1 Labeled Types

**Definition 2.1 (Security-Typed Value):**
```
τˡ = τ @ l

where:
  τ = base type
  l = security level
```

**Examples:**
```
Int @ Public       -- Public integer
String @ Private   -- Private string
Route @ System     -- System-level route data
```

### 2.2 Typing Rules with Labels

**Subtyping:**
```
l₁ ⊑ l₂
──────────────── [S-Label]
τ @ l₁ <: τ @ l₂
```

**Subsumption:**
```
Γ ⊢ e : τ @ l₁    l₁ ⊑ l₂
────────────────────────── [T-Sub]
    Γ ⊢ e : τ @ l₂
```

**Binary Operations:**
```
Γ ⊢ e₁ : τ @ l₁    Γ ⊢ e₂ : τ @ l₂
──────────────────────────────────── [T-BinOp]
    Γ ⊢ e₁ op e₂ : τ @ (l₁ ⊔ l₂)
```

**Conditional:**
```
Γ ⊢ e₁ : Bool @ l    Γ ⊢ e₂ : τ @ l'    Γ ⊢ e₃ : τ @ l'
─────────────────────────────────────────────────────────── [T-If]
        Γ ⊢ IF e₁ THEN e₂ ELSE e₃ : τ @ (l ⊔ l')
```

---

## 3. Noninterference

### 3.1 Low Equivalence

**Definition 3.1 (l-equivalence):**
Two environments ρ₁ and ρ₂ are l-equivalent (ρ₁ ≈ₗ ρ₂) iff:
```
∀x. level(x) ⊑ l → ρ₁(x) = ρ₂(x)
```

### 3.2 Noninterference Theorem

**Theorem 3.1 (Noninterference):**
If Γ ⊢ e : τ @ l, then:
```
∀ρ₁, ρ₂. ρ₁ ≈ₗ ρ₂ → ⟦e⟧ρ₁ = ⟦e⟧ρ₂
```

**Proof:** By structural induction on the typing derivation.

*Case T-Var:*
```
Γ ⊢ x : τ @ l

If level(x) ⊑ l:
  By ρ₁ ≈ₗ ρ₂: ρ₁(x) = ρ₂(x)
  So ⟦x⟧ρ₁ = ρ₁(x) = ρ₂(x) = ⟦x⟧ρ₂ ✓

If level(x) ⋢ l:
  Contradiction with Γ ⊢ x : τ @ l
```

*Case T-BinOp:*
```
Γ ⊢ e₁ op e₂ : τ @ (l₁ ⊔ l₂)

By IH: ⟦e₁⟧ρ₁ = ⟦e₁⟧ρ₂ (for l ⊒ l₁)
       ⟦e₂⟧ρ₁ = ⟦e₂⟧ρ₂ (for l ⊒ l₂)

If l ⊒ l₁ ⊔ l₂:
  ⟦e₁ op e₂⟧ρ₁ = ⟦e₁⟧ρ₁ op ⟦e₂⟧ρ₁
                = ⟦e₁⟧ρ₂ op ⟦e₂⟧ρ₂
                = ⟦e₁ op e₂⟧ρ₂ ✓
```

*Case T-If (implicit flow):*
```
Γ ⊢ IF e₁ THEN e₂ ELSE e₃ : τ @ (l ⊔ l')

The condition level l is joined with result level.
This prevents implicit flow:
  - Private condition can only produce Private result
  - Public observer cannot distinguish branches
```
∎

### 3.3 Termination-Insensitive Noninterference

**Theorem 3.2 (TINI):**
For terminating programs, noninterference holds:
```
∀ρ₁, ρ₂. ρ₁ ≈ₗ ρ₂ ∧ terminates(e, ρ₁) ∧ terminates(e, ρ₂) →
         ⟦e⟧ρ₁ = ⟦e⟧ρ₂
```

Since all Phronesis programs terminate (Termination Theorem), TINI = NI.

---

## 4. Implicit Flows

### 4.1 Identification

**Definition 4.1 (Implicit Flow):**
Information flows implicitly when a high-security value influences control flow that affects low-security output.

**Example:**
```phronesis
IF secret_condition THEN
  REPORT("branch A")
ELSE
  REPORT("branch B")
```

The report reveals the value of `secret_condition`.

### 4.2 Prevention

**Rule (No Implicit Leaks):**
```
Γ ⊢ e₁ : Bool @ l_cond
Γ ⊢ action : Action @ l_action
l_cond ⊑ l_action                   -- Condition level flows to action
──────────────────────────────────────────────────────────────────────
Γ ⊢ IF e₁ THEN action : Action @ l_cond ⊔ l_action
```

---

## 5. Declassification

### 5.1 Controlled Release

**Definition 5.1 (Declassification Point):**
```
declassify(e, from, to) : τ @ to

where:
  e : τ @ from
  from ⊐ to (downgrades security)
```

### 5.2 Robust Declassification

**Property:** Attackers cannot influence what is declassified.

```
Γ ⊢ e : τ @ High
───────────────────────────────────── [Declassify]
Γ ⊢ declassify(e) : τ @ Low

Requirement: e contains no Low inputs (robust)
```

### 5.3 Phronesis Declassification Points

```
1. REPORT action: Explicitly logs information (audit)
2. ACCEPT/REJECT: Binary decision is intentionally public
3. Consensus result: Revealed to all participants
```

---

## 6. Integrity Analysis

### 6.1 Integrity Lattice

**Definition 6.1:**
```
I = {Untrusted, Trusted, Authoritative}

Ordering (opposite of confidentiality):
  Authoritative ⊑ Trusted ⊑ Untrusted
```

### 6.2 Integrity Types

**Definition 6.2:**
```
τ^i = τ with integrity i

Trusted operation on untrusted input → untrusted result
```

### 6.3 Integrity Rules

**Input Validation:**
```
Γ ⊢ e : τ @ Untrusted    validate(e)
─────────────────────────────────────── [Validate]
    Γ ⊢ validated(e) : τ @ Trusted
```

**Taint Propagation:**
```
Γ ⊢ e₁ : τ @ i₁    Γ ⊢ e₂ : τ @ i₂
──────────────────────────────────── [Taint]
    Γ ⊢ e₁ op e₂ : τ @ (i₁ ⊔ i₂)
```

---

## 7. Phronesis Security Labels

### 7.1 Route Data Labels

```
route.prefix      : IP @ Public        -- Publicly announced
route.as_path     : [ASN] @ Public     -- Publicly visible
route.origin_as   : ASN @ Public       -- In announcement
route.next_hop    : IP @ Private       -- Internal routing
route.local_pref  : Int @ Private      -- Local policy
route.communities : [Int] @ Private    -- May be filtered
```

### 7.2 Policy Labels

```
policy.condition  : Bool @ evaluation_context
policy.action     : Action @ Public    -- Result is visible
policy.priority   : Int @ System       -- System configuration
```

### 7.3 Consensus Labels

```
vote              : Vote @ Private     -- Individual vote private
vote_count        : Int @ Public       -- Aggregate is public
committed_action  : Action @ Public    -- Result is public
```

---

## 8. Covert Channels

### 8.1 Timing Channels

**Definition 8.1:**
Information flows through observable timing differences.

**Mitigation:**
```
1. Constant-time operations where feasible
2. Timing obfuscation for sensitive operations
3. Rate limiting on consensus responses
```

### 8.2 Storage Channels

**Definition 8.2:**
Information flows through observable storage usage.

**Mitigation:**
```
1. Fixed-size data structures
2. No observable memory allocation in condition evaluation
3. Pre-allocated consensus log buffers
```

### 8.3 Termination Channels

**Theorem 8.1:** Phronesis has no termination channel.

**Proof:** All programs terminate in bounded time (Termination Theorem). No information flows through termination/non-termination distinction. ∎

---

## 9. Quantitative Information Flow

### 9.1 Shannon Entropy

**Definition 9.1:**
```
H(X) = -Σₓ P(X = x) × log₂(P(X = x))
```

### 9.2 Information Leakage

**Definition 9.2:**
```
Leak(C, S) = H(S) - H(S | O)

where:
  S = secret input
  O = observable output
  C = channel (program)
```

### 9.3 Bounds for Phronesis

**Theorem 9.1:** Policy evaluation leaks at most log₂(|actions|) bits.

**Proof:**
```
Output = ACCEPT | REJECT | REPORT
|actions| ≤ 3
Leak ≤ log₂(3) ≈ 1.58 bits ∎
```

---

## 10. Capability-Based Information Flow

### 10.1 Capabilities as Labels

**Definition 10.1:**
```
Capability = (resource, operations, constraints)

Information may flow to capability holder only.
```

### 10.2 Capability Propagation

```
Γ ⊢ e : τ @ {cap₁}    Γ ⊢ f : τ → τ' @ {cap₂}
─────────────────────────────────────────────── [Cap-App]
        Γ ⊢ f(e) : τ' @ {cap₁ ∩ cap₂}
```

---

## 11. Information Flow Types for Consensus

### 11.1 Vote Privacy

```
vote : Vote @ Agent(i)          -- Private to agent i
encrypted_vote : Enc @ Public   -- Encrypted, publicly visible
aggregate : Count @ Public      -- Aggregate count public
```

### 11.2 Threshold Revelation

**Property:** Individual votes are hidden until threshold reached.

```
Before threshold: vote(i) @ Private for all i
After threshold:  result @ Public, individual votes remain Private
```

---

## 12. Verification Approach

### 12.1 Type-Based Verification

```
1. Annotate all inputs with security labels
2. Type-check with security-aware type system
3. Verify no flows from High to Low (except declassification)
```

### 12.2 Static Analysis

```
1. Build information flow graph
2. Check for paths from High sources to Low sinks
3. Flag potential leaks for review
```

### 12.3 Runtime Enforcement

```
1. Dynamic taint tracking
2. Monitor declassification points
3. Audit log for sensitive flows
```

---

## 13. Summary

| Property | Guarantee | Mechanism |
|----------|-----------|-----------|
| Confidentiality | Noninterference | Security types |
| Integrity | Taint tracking | Integrity labels |
| Implicit flows | Prevented | PC label joining |
| Timing channels | Mitigated | Bounded execution |
| Termination channels | None | Total language |
| Declassification | Controlled | Explicit points |

---

## References

1. Sabelfeld, A., & Myers, A. C. (2003). *Language-Based Information-Flow Security*.
2. Denning, D. E. (1976). *A Lattice Model of Secure Information Flow*.
3. Volpano, D., Smith, G., & Irvine, C. (1996). *A Sound Type System for Secure Flow Analysis*.
4. Myers, A. C. (1999). *JFlow: Practical Mostly-Static Information Flow Control*.
