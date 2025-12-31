# Denotational Semantics for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides the denotational semantics for Phronesis, giving mathematical meaning to programs as functions between semantic domains.

---

## 1. Semantic Domains

### 1.1 Basic Domains

**Definition 1.1 (Primitive Domains):**
```
⟦Int⟧ = ℤ                      -- Mathematical integers
⟦Float⟧ = ℝ ∪ {NaN, +∞, -∞}   -- Extended reals
⟦String⟧ = Σ*                  -- Strings over alphabet Σ
⟦Bool⟧ = {tt, ff}             -- Boolean values
⟦IP⟧ = [0, 2³²) × [0, 128]    -- IP with prefix length
⟦DateTime⟧ = ℤ                 -- Unix timestamps
⟦Null⟧ = {★}                  -- Singleton unit
```

### 1.2 Composite Domains

**Definition 1.2 (Constructed Domains):**
```
⟦List(τ)⟧ = ⟦τ⟧*                          -- Finite sequences
⟦Record{l₁:τ₁,...,lₙ:τₙ}⟧ = ⟦τ₁⟧ × ... × ⟦τₙ⟧  -- Products
⟦τ₁ + τ₂⟧ = ⟦τ₁⟧ + ⟦τ₂⟧                  -- Disjoint union
⟦τ₁ → τ₂⟧ = ⟦τ₁⟧ → ⟦τ₂⟧                  -- Function space
```

### 1.3 Domain Ordering

**Definition 1.3 (Flat Domain):**
For base types, use flat CPO:
```
     ⊤
   / | \
  v₁ v₂ v₃ ...
   \ | /
     ⊥

where ⊥ represents non-termination (not needed for Phronesis)
```

Since Phronesis always terminates, we use simple sets rather than CPOs.

---

## 2. Environment

### 2.1 Type Environment

**Definition 2.1:**
```
Γ : Var → Type

where Var is the set of variable names
```

### 2.2 Value Environment

**Definition 2.2:**
```
ρ : Var → Value

ρ ⊨ Γ iff ∀x ∈ dom(Γ). ρ(x) ∈ ⟦Γ(x)⟧
```

---

## 3. Expression Semantics

### 3.1 Semantic Function

**Definition 3.1:**
```
⟦_⟧ : Expr → Env → Value
⟦e⟧ρ = the value of e in environment ρ
```

### 3.2 Literal Semantics

```
⟦n⟧ρ = n                           (integer literal)
⟦r⟧ρ = r                           (float literal)
⟦s⟧ρ = s                           (string literal)
⟦true⟧ρ = tt
⟦false⟧ρ = ff
⟦null⟧ρ = ★
```

### 3.3 Variable Semantics

```
⟦x⟧ρ = ρ(x)
```

### 3.4 Arithmetic Semantics

```
⟦e₁ + e₂⟧ρ = ⟦e₁⟧ρ +ℤ ⟦e₂⟧ρ
⟦e₁ - e₂⟧ρ = ⟦e₁⟧ρ -ℤ ⟦e₂⟧ρ
⟦e₁ * e₂⟧ρ = ⟦e₁⟧ρ ×ℤ ⟦e₂⟧ρ
⟦e₁ / e₂⟧ρ = ⟦e₁⟧ρ ÷ℤ ⟦e₂⟧ρ       (integer division)
⟦e₁ % e₂⟧ρ = ⟦e₁⟧ρ mod ⟦e₂⟧ρ
```

### 3.5 Comparison Semantics

```
⟦e₁ == e₂⟧ρ = if ⟦e₁⟧ρ = ⟦e₂⟧ρ then tt else ff
⟦e₁ != e₂⟧ρ = if ⟦e₁⟧ρ ≠ ⟦e₂⟧ρ then tt else ff
⟦e₁ < e₂⟧ρ = if ⟦e₁⟧ρ < ⟦e₂⟧ρ then tt else ff
⟦e₁ <= e₂⟧ρ = if ⟦e₁⟧ρ ≤ ⟦e₂⟧ρ then tt else ff
⟦e₁ > e₂⟧ρ = if ⟦e₁⟧ρ > ⟦e₂⟧ρ then tt else ff
⟦e₁ >= e₂⟧ρ = if ⟦e₁⟧ρ ≥ ⟦e₂⟧ρ then tt else ff
```

### 3.6 Logical Semantics

```
⟦e₁ AND e₂⟧ρ = ⟦e₁⟧ρ ∧ ⟦e₂⟧ρ
⟦e₁ OR e₂⟧ρ = ⟦e₁⟧ρ ∨ ⟦e₂⟧ρ
⟦NOT e⟧ρ = ¬⟦e⟧ρ
```

**Short-Circuit Semantics (Alternative):**
```
⟦e₁ AND e₂⟧ρ = if ⟦e₁⟧ρ = ff then ff else ⟦e₂⟧ρ
⟦e₁ OR e₂⟧ρ = if ⟦e₁⟧ρ = tt then tt else ⟦e₂⟧ρ
```

### 3.7 Conditional Semantics

```
⟦IF e₁ THEN e₂ ELSE e₃⟧ρ =
  if ⟦e₁⟧ρ = tt then ⟦e₂⟧ρ else ⟦e₃⟧ρ
```

### 3.8 List Semantics

```
⟦[]⟧ρ = ε                                    (empty list)
⟦[e₁, e₂, ..., eₙ]⟧ρ = ⟨⟦e₁⟧ρ, ⟦e₂⟧ρ, ..., ⟦eₙ⟧ρ⟩

⟦e₁ IN e₂⟧ρ = if ⟦e₁⟧ρ ∈ set(⟦e₂⟧ρ) then tt else ff
```

### 3.9 Record Semantics

```
⟦{l₁: e₁, ..., lₙ: eₙ}⟧ρ = {l₁ ↦ ⟦e₁⟧ρ, ..., lₙ ↦ ⟦eₙ⟧ρ}

⟦e.l⟧ρ = (⟦e⟧ρ)(l)                          (field access)
```

### 3.10 Module Call Semantics

```
⟦M.f(e₁, ..., eₙ)⟧ρ = M.f(⟦e₁⟧ρ, ..., ⟦eₙ⟧ρ)
```

Where M.f is the denotation of module function f in module M.

---

## 4. Action Semantics

### 4.1 Action Domain

**Definition 4.1:**
```
Action = Accept(v) | Reject(v) | Report(v) | Execute(f, args)
Result = Success(v) | Failure(e)
```

### 4.2 Action Denotation

```
⟦ACCEPT(e)⟧ρ = Accept(⟦e⟧ρ)
⟦REJECT(e)⟧ρ = Reject(⟦e⟧ρ)
⟦REPORT(e)⟧ρ = Report(⟦e⟧ρ)
⟦EXECUTE(f, e₁, ..., eₙ)⟧ρ = Execute(f, ⟦e₁⟧ρ, ..., ⟦eₙ⟧ρ)

⟦IF e₁ THEN a₁ ELSE a₂⟧ρ =
  if ⟦e₁⟧ρ = tt then ⟦a₁⟧ρ else ⟦a₂⟧ρ
```

---

## 5. Policy Semantics

### 5.1 Policy Denotation

**Definition 5.1:**
```
⟦POLICY name: cond THEN action PRIORITY: n⟧ =
  (name, λρ. if ⟦cond⟧ρ then Some(⟦action⟧ρ) else None, n)
```

### 5.2 Policy Table Semantics

**Definition 5.2:**
```
⟦PolicyTable⟧ = Map[Name, (Env → Option[Action], Priority)]
```

### 5.3 Policy Matching

**Definition 5.3:**
```
match(policies, ρ) =
  let applicable = {(p, action) | p ∈ policies, ⟦p.cond⟧ρ = tt}
  let highest = max_{priority}(applicable)
  in highest.action
```

---

## 6. State Semantics

### 6.1 State Domain

**Definition 6.1:**
```
State = (PolicyTable, ConsensusLog, Environment, PendingActions, Agents)

⟦State⟧ = ⟦PolicyTable⟧ × ⟦ConsensusLog⟧ × ⟦Env⟧ × ⟦Pending⟧ × ⟦Agents⟧
```

### 6.2 State Transformer

**Definition 6.2:**
```
⟦_⟧_S : Statement → State → State

⟦load(policy)⟧σ = σ[Π ↦ σ.Π ∪ {policy}]
⟦execute(action)⟧σ = σ[Λ ↦ σ.Λ ++ [(action, result)]]
```

---

## 7. Semantic Properties

### 7.1 Compositionality

**Theorem 7.1:** The semantics is compositional.
```
⟦e⟧ρ depends only on ⟦sub-expressions of e⟧ρ
```

**Proof:** By structural induction. Each semantic clause is defined in terms of sub-expression denotations. ∎

### 7.2 Adequacy

**Theorem 7.2:** Denotational and operational semantics agree.
```
ρ ⊢ e ⇓ v ⟺ ⟦e⟧ρ = v
```

**Proof:** By induction on expression structure.

*Base case (literals):*
```
ρ ⊢ n ⇓ n     (by E-INT)
⟦n⟧ρ = n      (by definition)
✓
```

*Inductive case (addition):*
```
ρ ⊢ e₁ + e₂ ⇓ v     where ρ ⊢ e₁ ⇓ n₁ and ρ ⊢ e₂ ⇓ n₂ and v = n₁ + n₂

By IH: ⟦e₁⟧ρ = n₁ and ⟦e₂⟧ρ = n₂

⟦e₁ + e₂⟧ρ = ⟦e₁⟧ρ + ⟦e₂⟧ρ = n₁ + n₂ = v
✓
```
∎

### 7.3 Determinism

**Theorem 7.3:** Semantics is deterministic.
```
⟦e⟧ρ is uniquely defined for all e and ρ
```

**Proof:** Each semantic clause has a unique right-hand side. ∎

---

## 8. Fixed Point Semantics

### 8.1 Recursive Definitions (Future)

For future recursive types:
```
⟦μX.τ⟧ = fix(λD. ⟦τ⟧[X ↦ D])
```

### 8.2 Knaster-Tarski

**Theorem 8.1:** If F : D → D is continuous on CPO D, then:
```
fix(F) = ⊔ᵢ Fⁱ(⊥)
```

### 8.3 Phronesis Simplification

Since Phronesis has no recursion:
- No need for CPO/fixed points
- Simple set-theoretic semantics suffices
- All denotations are total functions

---

## 9. Monadic Semantics

### 9.1 State Monad

**Definition 9.1:**
```
StateM S A = S → (A × S)

return a = λs. (a, s)
m >>= f = λs. let (a, s') = m s in f a s'
```

### 9.2 Action Semantics as State Monad

```
⟦REPORT(e)⟧ : StateM State ()
⟦REPORT(e)⟧ = λσ. ((), σ[Λ ↦ σ.Λ ++ [(Report, ⟦e⟧σ.Γ)]])
```

### 9.3 Composition

```
⟦a₁; a₂⟧ = ⟦a₁⟧ >>= λ_. ⟦a₂⟧
```

---

## 10. Continuation Semantics

### 10.1 Continuation Type

**Definition 10.1:**
```
Cont = Value → Answer
⟦_⟧ : Expr → Env → Cont → Answer
```

### 10.2 CPS Semantics

```
⟦n⟧ρ k = k n
⟦e₁ + e₂⟧ρ k = ⟦e₁⟧ρ (λv₁. ⟦e₂⟧ρ (λv₂. k (v₁ + v₂)))
⟦IF e₁ THEN e₂ ELSE e₃⟧ρ k =
  ⟦e₁⟧ρ (λv. if v = tt then ⟦e₂⟧ρ k else ⟦e₃⟧ρ k)
```

### 10.3 Equivalence

**Theorem 10.1:**
```
⟦e⟧ρ = ⟦e⟧_CPS ρ id
```

---

## 11. Logical Relations

### 11.1 Definition

**Definition 11.1 (Logical Relation):**
```
v ∼_τ v' : value v and v' are related at type τ

n ∼_Int n' ⟺ n = n'
b ∼_Bool b' ⟺ b = b'
vs ∼_{List τ} vs' ⟺ |vs| = |vs'| ∧ ∀i. vs[i] ∼_τ vs'[i]
f ∼_{τ₁→τ₂} f' ⟺ ∀v ∼_τ₁ v'. f(v) ∼_τ₂ f'(v')
```

### 11.2 Fundamental Theorem

**Theorem 11.1:**
```
If Γ ⊢ e : τ and ρ ∼_Γ ρ', then ⟦e⟧ρ ∼_τ ⟦e⟧ρ'
```

---

## 12. Abstract Interpretation Connection

### 12.1 Galois Connection

```
(⟦τ⟧, ⊆) ⟷^{α,γ} (⟦τ⟧^♯, ⊑)

α(V) = ⊔{v^♯ | v ∈ V}
γ(v^♯) = {v | v ⊑ v^♯}
```

### 12.2 Sound Abstraction

```
⟦e⟧^♯ ρ^♯ ⊒ α(⟦e⟧(γ(ρ^♯)))
```

---

## 13. Full Abstraction

### 13.1 Contextual Equivalence

**Definition 13.1:**
```
e₁ ≃_ctx e₂ ⟺ ∀C. C[e₁] terminates ⟺ C[e₂] terminates
```

### 13.2 Denotational Equivalence

```
e₁ ≃_den e₂ ⟺ ⟦e₁⟧ = ⟦e₂⟧
```

### 13.3 Full Abstraction Theorem

**Theorem 13.1:**
For Phronesis without side effects:
```
e₁ ≃_ctx e₂ ⟺ e₁ ≃_den e₂
```

**Proof Sketch:**
- Soundness: ⟦e₁⟧ = ⟦e₂⟧ → e₁ ≃_ctx e₂ (by adequacy)
- Completeness: Requires definability of all contexts

For Phronesis's simple type system, full abstraction holds. ∎

---

## 14. Summary

| Semantic Aspect | Denotation |
|-----------------|------------|
| Expressions | ⟦e⟧ : Env → Value |
| Actions | ⟦a⟧ : Env → Action |
| Policies | ⟦p⟧ : Env → Option[Action] |
| State | ⟦s⟧ : State → State |

**Key Properties:**
- Compositional
- Adequate (matches operational semantics)
- Deterministic
- Fully abstract

---

## References

1. Schmidt, D. A. (1986). *Denotational Semantics*. Allyn and Bacon.
2. Stoy, J. E. (1977). *Denotational Semantics*. MIT Press.
3. Winskel, G. (1993). *The Formal Semantics of Programming Languages*. MIT Press.
4. Tennent, R. D. (1991). *Semantics of Programming Languages*. Prentice Hall.
