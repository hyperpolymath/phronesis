# Unified Notation Guide for Phronesis Academic Documentation

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides a comprehensive notation reference for all Phronesis academic documentation, ensuring consistency across proofs, specifications, and formal models.

---

## 1. Type Theory Notation

### 1.1 Type Judgments

| Notation | Meaning |
|----------|---------|
| Γ ⊢ e : τ | Expression e has type τ in context Γ |
| Γ ⊢ τ type | τ is a well-formed type in context Γ |
| Γ ⊢ τ₁ <: τ₂ | τ₁ is a subtype of τ₂ |
| Γ, x : τ | Context extended with x of type τ |
| ⊢ e : τ | Closed typing (empty context) |

### 1.2 Types

| Notation | Meaning |
|----------|---------|
| Int, Bool, String | Base types |
| τ₁ → τ₂ | Function type |
| τ₁ × τ₂ | Product type |
| τ₁ + τ₂ | Sum type |
| List(τ) | List type |
| Record{f₁: τ₁, ...} | Record type |
| Any | Top type (⊤) |
| Never | Bottom type (⊥) |
| IP | IP address type |
| Action | Accept/Reject/Report |

### 1.3 Type Operations

| Notation | Meaning |
|----------|---------|
| τ₁ ⊔ τ₂ | Join (least upper bound) |
| τ₁ ⊓ τ₂ | Meet (greatest lower bound) |
| τ₁ <: τ₂ | Subtype relation |
| τ₁ ≡ τ₂ | Type equivalence |
| [τ/α]σ | Substitute τ for α in σ |

---

## 2. Logic Notation

### 2.1 Propositional Logic

| Notation | Meaning |
|----------|---------|
| ⊤, true | Truth |
| ⊥, false | Falsity |
| P ∧ Q | Conjunction (and) |
| P ∨ Q | Disjunction (or) |
| ¬P | Negation (not) |
| P → Q | Implication |
| P ↔ Q | Biconditional (iff) |
| P ⊢ Q | P entails Q |
| P ⊨ Q | P models Q |

### 2.2 First-Order Logic

| Notation | Meaning |
|----------|---------|
| ∀x. P(x) | Universal quantification |
| ∃x. P(x) | Existential quantification |
| ∃!x. P(x) | Unique existence |
| P[t/x] | Substitute t for x in P |

### 2.3 Temporal Logic

| Notation | Meaning |
|----------|---------|
| □P | Always P (G in CTL) |
| ◇P | Eventually P (F in CTL) |
| ○P | Next P (X in CTL) |
| P U Q | P until Q |
| P W Q | P weak until Q |
| A□P | On all paths, always P |
| E◇P | On some path, eventually P |

---

## 3. Semantic Notation

### 3.1 Big-Step Semantics

| Notation | Meaning |
|----------|---------|
| ρ ⊢ e ⇓ v | e evaluates to v in environment ρ |
| σ ⊢ s ⇓ σ' | Statement s transforms state σ to σ' |
| ⟨e, σ⟩ ⇓ v | Configuration evaluates to value |

### 3.2 Small-Step Semantics

| Notation | Meaning |
|----------|---------|
| e → e' | e steps to e' |
| e →* e' | e steps to e' in zero or more steps |
| e ↛ | e is in normal form (stuck or value) |
| E[e] | Evaluation context with hole |

### 3.3 Denotational Semantics

| Notation | Meaning |
|----------|---------|
| ⟦e⟧ρ | Meaning of e in environment ρ |
| ⟦τ⟧ | Semantic domain for type τ |
| ⊥_D | Bottom element of domain D |
| fix(f) | Least fixed point of f |

---

## 4. Set Theory Notation

### 4.1 Basic Sets

| Notation | Meaning |
|----------|---------|
| ∅ | Empty set |
| {a, b, c} | Set enumeration |
| {x \| P(x)} | Set comprehension |
| x ∈ A | Membership |
| x ∉ A | Non-membership |
| A ⊆ B | Subset |
| A ⊂ B | Proper subset |
| P(A) | Power set |

### 4.2 Set Operations

| Notation | Meaning |
|----------|---------|
| A ∪ B | Union |
| A ∩ B | Intersection |
| A \ B | Difference |
| A × B | Cartesian product |
| A ⊎ B | Disjoint union |
| ∪𝒜 | Union of family |
| ∩𝒜 | Intersection of family |

### 4.3 Cardinality

| Notation | Meaning |
|----------|---------|
| \|A\| | Cardinality of A |
| ℵ₀ | Countable infinity |
| 𝔠 | Continuum |
| A ≈ B | Same cardinality |

---

## 5. Function Notation

### 5.1 Functions

| Notation | Meaning |
|----------|---------|
| f : A → B | Function from A to B |
| f : A ⇀ B | Partial function |
| f(x) | Application |
| λx. e | Lambda abstraction |
| f ∘ g | Composition |
| id_A | Identity on A |
| f[x ↦ v] | Update f at x with v |

### 5.2 Function Properties

| Notation | Meaning |
|----------|---------|
| dom(f) | Domain |
| cod(f) | Codomain |
| ran(f) | Range |
| f↾A | Restriction to A |
| f injective | One-to-one |
| f surjective | Onto |
| f bijective | One-to-one correspondence |

---

## 6. Order Theory Notation

### 6.1 Orders

| Notation | Meaning |
|----------|---------|
| (P, ≤) | Partial order |
| x ≤ y | x is less than or equal to y |
| x < y | x is strictly less than y |
| x ⊑ y | x approximates y (domain theory) |
| x ⊏ y | x strictly approximates y |

### 6.2 Lattice Operations

| Notation | Meaning |
|----------|---------|
| x ⊔ y | Join (supremum, lub) |
| x ⊓ y | Meet (infimum, glb) |
| ⊥ | Bottom element |
| ⊤ | Top element |
| ⊔S | Join of set S |
| ⊓S | Meet of set S |

### 6.3 Fixed Points

| Notation | Meaning |
|----------|---------|
| lfp(f) | Least fixed point |
| gfp(f) | Greatest fixed point |
| μX. F(X) | Least fixed point |
| νX. F(X) | Greatest fixed point |

---

## 7. Category Theory Notation

### 7.1 Categories

| Notation | Meaning |
|----------|---------|
| Ob(C) | Objects of category C |
| Hom(A, B) | Morphisms from A to B |
| f : A → B | Morphism |
| g ∘ f | Composition |
| id_A | Identity morphism |

### 7.2 Functors

| Notation | Meaning |
|----------|---------|
| F : C → D | Functor |
| F(A) | F applied to object |
| F(f) | F applied to morphism |

### 7.3 Natural Transformations

| Notation | Meaning |
|----------|---------|
| η : F ⇒ G | Natural transformation |
| η_A : F(A) → G(A) | Component at A |

### 7.4 Limits

| Notation | Meaning |
|----------|---------|
| A × B | Product |
| A + B | Coproduct |
| 1 | Terminal object |
| 0 | Initial object |

---

## 8. Process Algebra Notation

### 8.1 CSP

| Notation | Meaning |
|----------|---------|
| STOP | Deadlock |
| SKIP | Successful termination |
| a → P | Prefix |
| P □ Q | External choice |
| P ⊓ Q | Internal choice |
| P ∥ Q | Parallel composition |
| P \\\\ A | Hiding |
| P ⊑ Q | Refinement |

### 8.2 CCS/π-Calculus

| Notation | Meaning |
|----------|---------|
| 0 | Nil process |
| α.P | Action prefix |
| P \| Q | Parallel |
| (νx)P | Restriction |
| !P | Replication |
| P ~ Q | Bisimilarity |

---

## 9. Hoare Logic Notation

### 9.1 Triples

| Notation | Meaning |
|----------|---------|
| {P} S {Q} | Partial correctness |
| [P] S [Q] | Total correctness |
| P = precondition | |
| Q = postcondition | |
| S = statement | |

### 9.2 Weakest Precondition

| Notation | Meaning |
|----------|---------|
| wp(S, Q) | Weakest precondition |
| sp(P, S) | Strongest postcondition |
| VC(P, S, Q) | Verification condition |

---

## 10. Separation Logic Notation

### 10.1 Assertions

| Notation | Meaning |
|----------|---------|
| emp | Empty heap |
| e₁ ↦ e₂ | Points-to |
| P ∗ Q | Separating conjunction |
| P -∗ Q | Magic wand |
| own(r, c) | Capability ownership |

### 10.2 Rules

| Notation | Meaning |
|----------|---------|
| {P} C {Q} | Triple (as in Hoare) |
| {P ∗ R} C {Q ∗ R} | Frame rule |

---

## 11. Cryptographic Notation

### 11.1 Primitives

| Notation | Meaning |
|----------|---------|
| {m}_k | Symmetric encryption |
| {\|m\|}_pk | Asymmetric encryption |
| sign(sk, m) | Digital signature |
| H(m) | Hash |
| pk(A), sk(A) | Key pair for A |

### 11.2 Security

| Notation | Meaning |
|----------|---------|
| A ⊢ m | Attacker knows m |
| negl(κ) | Negligible function |
| PPT | Probabilistic polynomial time |

---

## 12. Probability Notation

### 12.1 Basic

| Notation | Meaning |
|----------|---------|
| P(A) | Probability of A |
| P(A \| B) | Conditional probability |
| E[X] | Expected value |
| Var[X] | Variance |
| X ~ D | X distributed as D |

### 12.2 Distributions

| Notation | Meaning |
|----------|---------|
| Bernoulli(p) | Bernoulli distribution |
| Binomial(n, p) | Binomial distribution |
| Exp(λ) | Exponential distribution |
| N(μ, σ²) | Normal distribution |

---

## 13. Consensus Notation

### 13.1 Protocol

| Notation | Meaning |
|----------|---------|
| N | Number of agents |
| f | Maximum Byzantine agents |
| t | Threshold (usually ⌈(2N+1)/3⌉) |
| e | Epoch number |
| L | Leader |
| Aᵢ | Agent i |

### 13.2 Messages

| Notation | Meaning |
|----------|---------|
| PROPOSE(e, a) | Proposal message |
| VOTE(e, a, d) | Vote message |
| COMMIT(e, a, cert) | Commit message |

### 13.3 States

| Notation | Meaning |
|----------|---------|
| proposed(L, e, a) | L proposed a in epoch e |
| voted(A, e, a, d) | A voted d for a in e |
| committed(e, a) | Action a committed in e |

---

## 14. Phronesis-Specific Notation

### 14.1 Syntax

| Notation | Meaning |
|----------|---------|
| CONST x = e | Constant binding |
| POLICY name: c THEN a ELSE a' | Policy definition |
| IF c THEN e ELSE e' | Conditional |
| e₁ IN e₂ | Membership test |
| e.f | Field access |
| ACCEPT(m), REJECT(m) | Actions |

### 14.2 IP Addresses

| Notation | Meaning |
|----------|---------|
| a.b.c.d/n | CIDR prefix |
| IP(addr, len) | IP value |
| p₁ ⊆ p₂ | Prefix containment |

---

## 15. Proof Notation

### 15.1 Proof Structure

| Notation | Meaning |
|----------|---------|
| ∎ or QED | End of proof |
| □ | End of proof (alternative) |
| Claim: | Intermediate claim |
| Case: | Case analysis |
| IH | Induction hypothesis |
| By ... | Justification |

### 15.2 Inference Rules

```
  premises
─────────────── [RuleName]
  conclusion
```

---

## 16. Document Conventions

### 16.1 Definitions

**Definition N.M:** Formal definition with number.

### 16.2 Theorems

**Theorem N.M:** Major result.
**Lemma N.M:** Supporting result.
**Corollary N.M:** Direct consequence.
**Proposition N.M:** Minor result.

### 16.3 References

Format: Author (Year). *Title*. Venue.

---

## Quick Reference Card

```
Types:      τ₁ → τ₂, τ₁ × τ₂, List(τ), Record{...}
Subtyping:  τ₁ <: τ₂, τ₁ ⊔ τ₂, τ₁ ⊓ τ₂
Judgment:   Γ ⊢ e : τ
Evaluation: e ⇓ v, e → e', ⟦e⟧ρ
Logic:      ∀, ∃, ∧, ∨, ¬, →, ↔
Temporal:   □, ◇, ○, U
Sets:       ∈, ⊆, ∪, ∩, ×, P(A)
Orders:     ≤, ⊑, ⊔, ⊓, ⊥, ⊤
Categories: →, ∘, ⇒
Processes:  →, □, ⊓, ∥, ~
Separation: ∗, -∗, ↦, emp
Hoare:      {P} S {Q}, wp, sp
Crypto:     {}_k, sign, H
Probability: P(), E[], Var[]
Consensus:  N, f, t, PROPOSE, VOTE, COMMIT
```
