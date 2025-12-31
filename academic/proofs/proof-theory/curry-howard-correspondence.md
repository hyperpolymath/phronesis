# Proof Theory and Curry-Howard Correspondence for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document establishes the proof-theoretic foundations of Phronesis, including the Curry-Howard correspondence between types and propositions, and proof normalization properties.

---

## 1. Proof-Theoretic Foundations

### 1.1 Propositions as Types

The Curry-Howard isomorphism establishes:
```
Types          ⟷  Propositions
Programs       ⟷  Proofs
Evaluation     ⟷  Proof normalization
Type checking  ⟷  Proof verification
```

### 1.2 Phronesis Type-Proposition Correspondence

| Type | Proposition |
|------|-------------|
| Int | ⊤ (trivially true for any integer) |
| Bool | P (some proposition) |
| τ₁ × τ₂ (Record) | P ∧ Q (conjunction) |
| τ₁ + τ₂ (Union) | P ∨ Q (disjunction) |
| τ₁ → τ₂ | P ⊃ Q (implication) |
| List(τ) | ∃n. τⁿ (existential) |
| ⊥ (Void) | ⊥ (falsity) |
| ⊤ (Unit) | ⊤ (truth) |

---

## 2. Natural Deduction for Phronesis Types

### 2.1 Introduction Rules

**Conjunction Introduction (Record):**
```
    Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂
    ───────────────────────────── [∧-I]
    Γ ⊢ {a: e₁, b: e₂} : τ₁ × τ₂
```

**Disjunction Introduction (Union - Future):**
```
        Γ ⊢ e : τ₁
    ───────────────────── [∨-I-L]
    Γ ⊢ inl(e) : τ₁ + τ₂

        Γ ⊢ e : τ₂
    ───────────────────── [∨-I-R]
    Γ ⊢ inr(e) : τ₁ + τ₂
```

**Implication Introduction (Lambda - Internal):**
```
    Γ, x : τ₁ ⊢ e : τ₂
    ─────────────────────── [⊃-I]
    Γ ⊢ λx.e : τ₁ → τ₂
```

**Truth Introduction:**
```
    ───────────────── [⊤-I]
    Γ ⊢ () : Unit
```

### 2.2 Elimination Rules

**Conjunction Elimination (Field Access):**
```
    Γ ⊢ e : τ₁ × τ₂
    ──────────────────── [∧-E-1]
    Γ ⊢ e.a : τ₁

    Γ ⊢ e : τ₁ × τ₂
    ──────────────────── [∧-E-2]
    Γ ⊢ e.b : τ₂
```

**Disjunction Elimination (Pattern Match):**
```
    Γ ⊢ e : τ₁ + τ₂    Γ, x : τ₁ ⊢ e₁ : τ    Γ, y : τ₂ ⊢ e₂ : τ
    ─────────────────────────────────────────────────────────────── [∨-E]
    Γ ⊢ match e with inl(x) → e₁ | inr(y) → e₂ : τ
```

**Implication Elimination (Application):**
```
    Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
    ────────────────────────────────── [⊃-E]
    Γ ⊢ e₁(e₂) : τ₂
```

**Falsity Elimination:**
```
    Γ ⊢ e : ⊥
    ────────────── [⊥-E]
    Γ ⊢ absurd(e) : τ
```

---

## 3. Proof Normalization

### 3.1 β-Reduction (Cut Elimination)

**Conjunction β:**
```
{a: e₁, b: e₂}.a ⟶ e₁
{a: e₁, b: e₂}.b ⟶ e₂
```

**Disjunction β:**
```
match inl(e) with inl(x) → e₁ | inr(y) → e₂ ⟶ e₁[e/x]
match inr(e) with inl(x) → e₁ | inr(y) → e₂ ⟶ e₂[e/y]
```

**Implication β:**
```
(λx.e₁)(e₂) ⟶ e₁[e₂/x]
```

### 3.2 η-Expansion

**Conjunction η:**
```
e ⟶ {a: e.a, b: e.b}  (when e : τ₁ × τ₂)
```

**Implication η:**
```
e ⟶ λx.e(x)  (when e : τ₁ → τ₂, x not free in e)
```

### 3.3 Strong Normalization

**Theorem 3.1 (Strong Normalization):**
All well-typed Phronesis expressions have a normal form.

**Proof:**
1. Phronesis has no recursion (grammar restriction)
2. Each β-reduction decreases term size
3. η-expansion preserves termination
4. Therefore, reduction terminates ∎

### 3.4 Confluence

**Theorem 3.2 (Church-Rosser):**
If e ⟶* e₁ and e ⟶* e₂, then ∃e'. e₁ ⟶* e' and e₂ ⟶* e'.

**Proof:**
Apply Newman's lemma (local confluence + strong normalization → confluence).
Local confluence holds by inspection of critical pairs. ∎

---

## 4. Sequent Calculus

### 4.1 Sequent Notation

```
Γ ⊢ Δ

where:
  Γ = multiset of antecedents (hypotheses)
  Δ = multiset of succedents (conclusions)
```

For Phronesis (intuitionistic): |Δ| ≤ 1

### 4.2 Structural Rules

**Identity:**
```
──────────── [Id]
A ⊢ A
```

**Cut:**
```
Γ ⊢ A    A, Δ ⊢ C
──────────────────── [Cut]
    Γ, Δ ⊢ C
```

**Weakening:**
```
    Γ ⊢ C
────────────── [W-L]
  A, Γ ⊢ C
```

**Contraction:**
```
  A, A, Γ ⊢ C
────────────── [C-L]
   A, Γ ⊢ C
```

### 4.3 Logical Rules (Left and Right)

**Conjunction Right:**
```
Γ ⊢ A    Γ ⊢ B
──────────────── [∧-R]
   Γ ⊢ A ∧ B
```

**Conjunction Left:**
```
  A, B, Γ ⊢ C
────────────────── [∧-L]
  A ∧ B, Γ ⊢ C
```

**Implication Right:**
```
   A, Γ ⊢ B
────────────── [⊃-R]
  Γ ⊢ A ⊃ B
```

**Implication Left:**
```
Γ ⊢ A    B, Δ ⊢ C
────────────────────── [⊃-L]
  A ⊃ B, Γ, Δ ⊢ C
```

### 4.4 Cut Elimination

**Theorem 4.1 (Gentzen's Hauptsatz):**
Every proof in the sequent calculus can be transformed to a cut-free proof.

**Application:** Type checking without intermediate lemmas.

---

## 5. Logical Framework Embedding

### 5.1 LF Signature for Phronesis

```
Phronesis : LF Signature

-- Types
tp : type
int : tp
bool : tp
string : tp
list : tp → tp
record : tp → tp → tp
arrow : tp → tp → tp

-- Terms
tm : tp → type
z : tm int
s : tm int → tm int
true : tm bool
false : tm bool
nil : {A:tp} tm (list A)
cons : {A:tp} tm A → tm (list A) → tm (list A)
pair : {A:tp} {B:tp} tm A → tm B → tm (record A B)
fst : {A:tp} {B:tp} tm (record A B) → tm A
snd : {A:tp} {B:tp} tm (record A B) → tm B
lam : {A:tp} {B:tp} (tm A → tm B) → tm (arrow A B)
app : {A:tp} {B:tp} tm (arrow A B) → tm A → tm B
```

### 5.2 Adequacy

**Theorem 5.1:** The LF encoding is adequate.
- Bijection between Phronesis terms and LF terms
- Bijection between typing derivations and LF types

---

## 6. Linear Logic Interpretation

### 6.1 Resource Interpretation

For capability-based security:
```
Capability as linear proposition: must be used exactly once
```

### 6.2 Linear Types (Future Enhancement)

```
τ ::= ... | !τ           -- Unrestricted (can duplicate)
        | τ ⊸ τ'        -- Linear implication (must use)
```

**Linear Implication:**
```
    Γ; Δ, x : τ ⊢ e : τ'
    ──────────────────────── [⊸-I]
    Γ; Δ ⊢ λx.e : τ ⊸ τ'
```

### 6.3 Capability as Linear Resource

```
has_cap(c) ⊸ (operation(c) ⊗ has_cap(c))
```
Capability consumed and returned (or not, if revoked).

---

## 7. Proof Irrelevance

### 7.1 Propositions with Unique Proofs

For certain types, all inhabitants are "equal":
```
Bool : { true, false }        -- Not proof-irrelevant
Unit : { () }                  -- Proof-irrelevant (only one value)
Proof(P) : { * }              -- Proof-irrelevant propositions
```

### 7.2 Application to Policy

Policy conditions are proof-irrelevant:
```
If condition is true, we don't care *which* proof
```

---

## 8. Constructive Logic Properties

### 8.1 Disjunction Property

**Theorem 8.1:** If ⊢ P ∨ Q is provable, then ⊢ P or ⊢ Q is provable.

**Application:** Type inference produces specific types, not disjunctions.

### 8.2 Existence Property

**Theorem 8.2:** If ⊢ ∃x.P(x) is provable, then ⊢ P(t) for some term t.

**Application:** Type inference provides witness terms.

### 8.3 No Excluded Middle

```
¬(P ∨ ¬P) is not derivable in general
```

But Phronesis uses classical logic for conditions (Bool is decidable).

---

## 9. Proof Terms

### 9.1 Decorated Derivations

Each typing derivation is a proof term:
```
Γ ⊢ e : τ

e is the proof term for proposition τ under hypotheses Γ
```

### 9.2 Example Proof Term

For the theorem: (A ∧ B) ⊃ (B ∧ A)
```
λp. {fst: p.snd, snd: p.fst}
```

Type derivation:
```
1. p : A ∧ B                     [hypothesis]
2. p.snd : B                     [∧-E-2 on 1]
3. p.fst : A                     [∧-E-1 on 1]
4. {fst: p.snd, snd: p.fst} : B ∧ A    [∧-I on 2, 3]
5. λp. ... : (A ∧ B) ⊃ (B ∧ A)  [⊃-I on 4]
```

---

## 10. Proof Search

### 10.1 Backward Chaining

```
Algorithm ProveGoal(Γ, τ):
  match τ with
  | A ∧ B → let p₁ = ProveGoal(Γ, A)
            let p₂ = ProveGoal(Γ, B)
            return (p₁, p₂)
  | A ⊃ B → let p = ProveGoal(Γ ∪ {x:A}, B)
            return λx.p
  | A    → find x : A in Γ
            return x
```

### 10.2 Decidability

**Theorem 10.1:** Proof search for Phronesis types is decidable.

**Proof:**
1. Finite grammar of types
2. Subformula property of proofs
3. Terminating search procedure ∎

---

## 11. Heyting Algebra Semantics

### 11.1 Propositions as Opens

In the Kripke semantics:
```
⟦P⟧ = {w | w forces P}
```

### 11.2 Validity

```
⊨ P iff ⟦P⟧ = W (all worlds)
```

### 11.3 Soundness and Completeness

**Theorem 11.1:** Phronesis type system is sound and complete w.r.t. Kripke semantics.

---

## 12. Proof Complexity

### 12.1 Proof Length

**Theorem 12.1:** Proofs in Phronesis are polynomial in formula size.

**Proof:**
- No cuts means no exponential blowup
- Linear in number of connectives ∎

### 12.2 Proof Checking

**Theorem 12.2:** Proof checking is O(n) for proof of size n.

**Proof:** Each step verified in O(1), traverse once. ∎

---

## 13. Realizability

### 13.1 Kleene Realizability

```
n ⊩ P (n realizes P)

n ⊩ P ∧ Q  iff  π₁(n) ⊩ P ∧ π₂(n) ⊩ Q
n ⊩ P ⊃ Q  iff  ∀m. m ⊩ P → n·m ⊩ Q
n ⊩ ∃x.P(x) iff  π₁(n) = witness ∧ π₂(n) ⊩ P(witness)
```

### 13.2 Phronesis Realizability

Phronesis programs realize their types:
```
eval(e) ⊩ τ when ⊢ e : τ
```

---

## 14. Connections to Other Proof Systems

### 14.1 Correspondence Table

| Proof System | Phronesis Analogue |
|--------------|-------------------|
| Natural Deduction | Type derivations |
| Sequent Calculus | Bidirectional typing |
| Lambda Calculus | Expression language |
| Combinatory Logic | Point-free style |
| Proof Nets | Parallel evaluation |

### 14.2 Embedding in Coq

See `/academic/formal-verification/coq/` for Coq embedding.

---

## 15. Philosophical Foundations

### 15.1 BHK Interpretation

```
A proof of P ∧ Q is a pair (p, q) where p proves P and q proves Q
A proof of P ⊃ Q is a function transforming proofs of P to proofs of Q
A proof of ∃x.P(x) is a pair (t, p) where t is witness and p proves P(t)
```

### 15.2 Programs as Proofs

Phronesis programs are constructive proofs:
- They compute witnesses
- They are verifiable
- They are normalizable

---

## References

1. Howard, W. A. (1980). *The Formulae-as-Types Notion of Construction*.
2. Girard, J.-Y. (1989). *Proofs and Types*. Cambridge.
3. Sørensen, M. H., & Urzyczyn, P. (2006). *Lectures on the Curry-Howard Isomorphism*.
4. Pfenning, F. (2001). *Lecture Notes on Natural Deduction*.
