# Model Theory Specification for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides model-theoretic semantics for Phronesis, including structures, satisfaction, and model-theoretic properties.

---

## 1. First-Order Signature

### 1.1 Signature Definition

**Definition 1.1 (Phronesis Signature):**
```
Σ_Phr = (S, F, P)

S = {Int, Float, String, Bool, IP, DateTime, List, Record, Action}  -- Sorts

F = {                                    -- Function symbols
  +, -, *, /, % : Int × Int → Int
  +, -, *, / : Float × Float → Float
  AND, OR : Bool × Bool → Bool
  NOT : Bool → Bool
  == : τ × τ → Bool (for each τ)
  <, >, ≤, ≥ : Numeric × Numeric → Bool
  IN : τ × List(τ) → Bool
  . : Record × FieldName → τ
  ACCEPT, REJECT : String → Action
  REPORT : String → Action
}

P = {                                    -- Predicate symbols
  valid : Route → Bool
  bogon : IP → Bool
  in_window : DateTime × DateTime × DateTime → Bool
}
```

### 1.2 Many-Sorted Logic

Phronesis uses many-sorted first-order logic:
```
Terms:     t ::= x | c | f(t₁, ..., tₙ)
Formulas:  φ ::= P(t₁, ..., tₙ) | t₁ = t₂ | ¬φ | φ ∧ ψ | φ ∨ ψ | ∃x:s.φ | ∀x:s.φ
```

---

## 2. Structures

### 2.1 Phronesis Structure

**Definition 2.1 (Σ-Structure):**
```
M = (|M|, I)

|M| = {D_s | s ∈ S}           -- Domain family (one per sort)
I : interpretation function

Domains:
  D_Int = ℤ                   -- Integers
  D_Float = ℝ ∪ {NaN, ±∞}    -- IEEE 754 floats
  D_String = Σ*              -- Unicode strings
  D_Bool = {true, false}
  D_IP = IPv4 ∪ IPv6         -- IP addresses
  D_DateTime = ℤ             -- Unix timestamps
  D_List(τ) = D_τ*           -- Finite sequences
  D_Record = finite maps
  D_Action = {Accept, Reject, Report} × D_String
```

### 2.2 Interpretation Function

**Function Interpretation:**
```
I(+_Int)(n₁, n₂) = n₁ + n₂ (integer addition)
I(AND)(b₁, b₂) = b₁ ∧ b₂ (boolean conjunction)
I(==_τ)(v₁, v₂) = (v₁ = v₂) (equality on τ)
I(IN)(v, L) = v ∈ L (list membership)
I(.)(r, f) = r(f) (field access)
I(ACCEPT)(s) = (Accept, s)
```

**Predicate Interpretation:**
```
I(valid)(r) ⟺ RPKI validation succeeds for r
I(bogon)(ip) ⟺ ip ∈ ReservedRanges
I(in_window)(t, start, end) ⟺ start ≤ t ≤ end
```

---

## 3. Satisfaction Relation

### 3.1 Variable Assignment

**Definition 3.1:**
```
σ : Var → |M|

such that σ(x) ∈ D_{sort(x)}
```

### 3.2 Term Evaluation

**Definition 3.2:**
```
⟦x⟧_σ = σ(x)
⟦c⟧_σ = I(c)
⟦f(t₁, ..., tₙ)⟧_σ = I(f)(⟦t₁⟧_σ, ..., ⟦tₙ⟧_σ)
```

### 3.3 Satisfaction

**Definition 3.3 (M ⊨_σ φ):**
```
M ⊨_σ P(t₁, ..., tₙ)  iff  I(P)(⟦t₁⟧_σ, ..., ⟦tₙ⟧_σ) = true
M ⊨_σ t₁ = t₂         iff  ⟦t₁⟧_σ = ⟦t₂⟧_σ
M ⊨_σ ¬φ              iff  M ⊭_σ φ
M ⊨_σ φ ∧ ψ           iff  M ⊨_σ φ and M ⊨_σ ψ
M ⊨_σ φ ∨ ψ           iff  M ⊨_σ φ or M ⊨_σ ψ
M ⊨_σ ∃x:s.φ          iff  M ⊨_σ[x↦d] φ for some d ∈ D_s
M ⊨_σ ∀x:s.φ          iff  M ⊨_σ[x↦d] φ for all d ∈ D_s
```

### 3.4 Validity and Satisfiability

**Definition 3.4:**
```
φ is valid (⊨ φ)          iff  M ⊨ φ for all structures M
φ is satisfiable          iff  M ⊨ φ for some structure M
φ is unsatisfiable        iff  no structure satisfies φ
```

---

## 4. Theories

### 4.1 Phronesis Theory

**Definition 4.1 (T_Phr):**
The theory of Phronesis consists of axioms:

**Integer Axioms (Presburger Arithmetic):**
```
∀x. x + 0 = x
∀x, y. x + y = y + x
∀x, y, z. (x + y) + z = x + (y + z)
∀x. x * 0 = 0
∀x. x * 1 = x
...
```

**Boolean Axioms:**
```
∀x. x AND true = x
∀x. x AND false = false
∀x. x OR true = true
∀x. x OR false = x
∀x. NOT (NOT x) = x
```

**List Axioms:**
```
∀x, L. x IN [] = false
∀x, y, L. x IN (y :: L) = (x = y) OR (x IN L)
```

**Record Axioms:**
```
∀r, f. (r with f = v).f = v
∀r, f, g. f ≠ g → (r with f = v).g = r.g
```

### 4.2 Policy Theory

**Definition 4.2 (T_Policy):**
Additional axioms for network policies:

```
∀r. valid(r) ∨ invalid(r) ∨ not_found(r)
∀r. valid(r) → ¬invalid(r)
∀r. bogon(r.prefix) → invalid(r)
∀r. has_loop(r.as_path) → invalid(r)
```

---

## 5. Model Properties

### 5.1 Soundness

**Theorem 5.1:** If Γ ⊢ e : τ, then for all models M and assignments σ,
⟦e⟧_σ ∈ D_τ.

**Proof:** By induction on typing derivation. Each typing rule corresponds to correct domain membership. ∎

### 5.2 Completeness (Relative)

**Theorem 5.2:** If M ⊨ φ for all models of T_Phr, then T_Phr ⊢ φ.

**Proof:** Standard completeness for first-order logic (Gödel). ∎

### 5.3 Decidability

**Theorem 5.3:** The quantifier-free fragment of T_Phr is decidable.

**Proof:**
1. Quantifier-free formulas have finite truth tables
2. Each atom is decidable (computable functions)
3. Boolean combination is decidable ∎

---

## 6. Herbrand Models

### 6.1 Herbrand Universe

**Definition 6.1:**
```
H = all ground terms over Σ_Phr

H_Int = {0, 1, -1, 2, -2, ...}
H_Bool = {true, false}
H_List(τ) = {[], [t₁], [t₁, t₂], ...} for t_i ∈ H_τ
```

### 6.2 Herbrand Model

**Definition 6.2:**
A Herbrand model interprets each ground term as itself.

**Theorem 6.1:** If φ is satisfiable, it has a Herbrand model.

---

## 7. Definability

### 7.1 Definable Sets

**Definition 7.1:**
A set S ⊆ D^n is definable iff ∃φ(x₁,...,xₙ). S = {(d₁,...,dₙ) | M ⊨ φ[d₁,...,dₙ]}

### 7.2 Definable Functions

**Definition 7.2:**
A function f : D^n → D is definable iff its graph is definable.

**Example:** Addition is definable:
```
Graph(+) = {(x, y, z) | z = x + y}
```

### 7.3 Phronesis Definability

**Theorem 7.1:** All Phronesis operations are definable in T_Phr.

---

## 8. Elementary Equivalence

### 8.1 Definition

**Definition 8.1:**
M ≡ N iff for all sentences φ: M ⊨ φ ↔ N ⊨ φ

### 8.2 Isomorphism

**Definition 8.2:**
M ≅ N iff there exists a bijection h : |M| → |N| preserving structure.

**Theorem 8.1:** M ≅ N → M ≡ N (but not conversely in general).

---

## 9. Compactness

### 9.1 Compactness Theorem

**Theorem 9.1:** If every finite subset of Γ is satisfiable, then Γ is satisfiable.

### 9.2 Application: Infinite Models

**Corollary 9.1:** If Γ has arbitrarily large finite models, it has an infinite model.

**Application:** The AS graph theory has infinite models (arbitrary network sizes).

---

## 10. Löwenheim-Skolem

### 10.1 Downward Löwenheim-Skolem

**Theorem 10.1:** If Γ has an infinite model, it has a countable model.

### 10.2 Upward Löwenheim-Skolem

**Theorem 10.2:** If Γ has an infinite model, it has models of all cardinalities ≥ |Γ| + ℵ₀.

### 10.3 Application

**Corollary 10.1:** Phronesis semantics is not categorical (many non-isomorphic models).

---

## 11. Quantifier Elimination

### 11.1 QE for Presburger Arithmetic

**Theorem 11.1:** Presburger arithmetic admits quantifier elimination.

Every formula is equivalent to a quantifier-free formula.

### 11.2 QE Algorithm

```
Eliminate ∃x. φ where φ is DNF:
  1. Collect constraints on x
  2. Substitute boundary values
  3. Remove x
```

### 11.3 Application to Phronesis

**Theorem 11.2:** Policy conditions over integers admit QE.

**Proof:** Policy conditions use Presburger-definable operations. ∎

---

## 12. Interpolation

### 12.1 Craig Interpolation

**Theorem 12.1:** If φ ⊢ ψ, there exists θ such that:
1. φ ⊢ θ
2. θ ⊢ ψ
3. Var(θ) ⊆ Var(φ) ∩ Var(ψ)

### 12.2 Application: Modular Verification

Interpolants connect module specifications:
```
Pre(module1) → Post(module1) = Pre(module2)
```

---

## 13. Ultraproducts

### 13.1 Definition

**Definition 13.1:**
Given models (M_i)_{i∈I} and ultrafilter U:
```
∏_U M_i = equivalence classes of (m_i)_{i∈I} under U-equivalence
```

### 13.2 Łoś's Theorem

**Theorem 13.1:**
∏_U M_i ⊨ φ[(m_i^1), ..., (m_i^n)] iff {i | M_i ⊨ φ[m_i^1, ..., m_i^n]} ∈ U

### 13.3 Application: Non-Standard Models

Ultraproducts construct non-standard integers (infinite integers).

---

## 14. Finite Model Theory

### 14.1 Failure of Compactness

**Theorem 14.1:** Compactness fails for finite structures.

**Proof:** Consider {φ_n | n ∈ ℕ} where φ_n says "at least n elements".
Every finite subset is satisfiable (by sufficiently large finite model).
But the whole set has no finite model. ∎

### 14.2 0-1 Law

**Theorem 14.2:** For many graph properties, probability in random finite graph → 0 or 1 as n → ∞.

### 14.3 Application to Networks

**Theorem 14.3:** AS graph properties have asymptotic probabilities.

---

## 15. Model Checking Connection

### 15.1 Modal Logic Connection

Kripke models for temporal properties:
```
M = (W, R, V)

W = set of states (worlds)
R = accessibility relation
V = valuation (world → propositions)
```

### 15.2 Phronesis State as World

```
w = (PolicyTable, ConsensusLog, Environment, ...)
R = transition relation (evaluation steps)
V(w) = {propositions true in state w}
```

---

## 16. Semantic Domains

### 16.1 Domain Equations

Recursive types (future) would require:
```
List(τ) ≅ 1 + τ × List(τ)
Tree(τ) ≅ 1 + τ × Tree(τ) × Tree(τ)
```

### 16.2 Solution by CPO

In domain theory:
```
D = μX. F(X)

where F is a continuous functor on CPO
```

---

## 17. Summary

**Model-Theoretic Properties of Phronesis:**

| Property | Status | Notes |
|----------|--------|-------|
| Soundness | ✓ | Typing implies semantic membership |
| Decidability (QF) | ✓ | Quantifier-free decidable |
| QE (integers) | ✓ | Via Presburger |
| Compactness | ✓ | Standard FOL |
| Categoricity | ✗ | Multiple models |

---

## References

1. Hodges, W. (1993). *Model Theory*. Cambridge.
2. Chang, C. C., & Keisler, H. J. (1990). *Model Theory*. North-Holland.
3. Marker, D. (2002). *Model Theory: An Introduction*. Springer.
4. Enderton, H. B. (2001). *A Mathematical Introduction to Logic*. Academic Press.
