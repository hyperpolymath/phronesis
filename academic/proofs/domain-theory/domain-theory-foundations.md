# Domain Theory Foundations for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document establishes the domain-theoretic foundations for Phronesis semantics, including complete partial orders, continuity, and fixed-point theory.

---

## 1. Complete Partial Orders

### 1.1 Basic Definitions

**Definition 1.1 (Partial Order):**
A partial order (D, ⊑) is a set D with binary relation ⊑ satisfying:
```
Reflexivity:     ∀x. x ⊑ x
Antisymmetry:    ∀x,y. x ⊑ y ∧ y ⊑ x → x = y
Transitivity:    ∀x,y,z. x ⊑ y ∧ y ⊑ z → x ⊑ z
```

**Definition 1.2 (Chain):**
A chain in (D, ⊑) is a sequence (dᵢ)ᵢ∈ℕ where:
```
d₀ ⊑ d₁ ⊑ d₂ ⊑ ... ⊑ dₙ ⊑ ...
```

**Definition 1.3 (Least Upper Bound):**
```
⊔{dᵢ | i ∈ I} = d iff:
  1. ∀i. dᵢ ⊑ d                    (upper bound)
  2. ∀d'. (∀i. dᵢ ⊑ d') → d ⊑ d'  (least)
```

**Definition 1.4 (Complete Partial Order - CPO):**
(D, ⊑) is a CPO iff:
1. D has a least element ⊥
2. Every chain has a least upper bound

**Definition 1.5 (Pointed CPO - CPPO):**
A CPO with explicit bottom element.

### 1.2 Examples

**Flat Domain:**
```
D⊥ = D ∪ {⊥} with ordering:
  ⊥ ⊑ d for all d ∈ D
  d ⊑ d' iff d = d' (for d, d' ∈ D)

        d₁    d₂    d₃    ...
         \    |    /
          \   |   /
           \  |  /
             ⊥
```

**Lifted Domain:**
```
D_⊥ = D ∪ {⊥}
```

**Function Space:**
```
[D → E] = {f : D → E | f is continuous}
f ⊑ g iff ∀d. f(d) ⊑ g(d)
```

**Product Domain:**
```
D × E with (d₁, e₁) ⊑ (d₂, e₂) iff d₁ ⊑ d₂ ∧ e₁ ⊑ e₂
```

**Sum Domain:**
```
D + E = {inl(d) | d ∈ D} ∪ {inr(e) | e ∈ E} ∪ {⊥}
inl(d₁) ⊑ inl(d₂) iff d₁ ⊑ d₂
inr(e₁) ⊑ inr(e₂) iff e₁ ⊑ e₂
⊥ ⊑ x for all x
```

---

## 2. Continuity

### 2.1 Scott Continuity

**Definition 2.1 (Monotonicity):**
f : D → E is monotone iff:
```
∀d, d'. d ⊑ d' → f(d) ⊑ f(d')
```

**Definition 2.2 (Scott Continuity):**
f : D → E is Scott-continuous iff:
```
f is monotone AND
∀ chains (dᵢ). f(⊔ᵢ dᵢ) = ⊔ᵢ f(dᵢ)
```

**Theorem 2.1:** Continuous functions preserve limits of chains.

**Proof:**
```
Let (dᵢ) be a chain in D.
f(⊔ᵢ dᵢ) = ⊔ᵢ f(dᵢ)     (by definition of continuity)

The RHS is the limit of chain (f(dᵢ)) since:
  f(d₀) ⊑ f(d₁) ⊑ ... (by monotonicity)
∎
```

### 2.2 Strict Functions

**Definition 2.3 (Strictness):**
f : D → E is strict iff f(⊥_D) = ⊥_E

### 2.3 Continuous Operations

**Theorem 2.2:** The following are continuous:
1. Identity: id(d) = d
2. Constant: const_c(d) = c
3. Projection: π₁(d, e) = d
4. Pairing: ⟨f, g⟩(d) = (f(d), g(d))
5. Composition: (g ∘ f)(d) = g(f(d))
6. Application: apply(f, d) = f(d)
7. Currying: curry(f)(d)(e) = f(d, e)

**Proof (Composition):**
```
Let (dᵢ) be a chain.
(g ∘ f)(⊔ᵢ dᵢ) = g(f(⊔ᵢ dᵢ))
                = g(⊔ᵢ f(dᵢ))     (f continuous)
                = ⊔ᵢ g(f(dᵢ))     (g continuous)
                = ⊔ᵢ (g ∘ f)(dᵢ)
∎
```

---

## 3. Fixed Point Theory

### 3.1 Tarski's Fixed Point Theorem

**Theorem 3.1 (Knaster-Tarski):**
Let f : L → L be monotone on complete lattice L.
Then f has a least fixed point:
```
lfp(f) = ⊓{x | f(x) ⊑ x}
```

### 3.2 Kleene's Fixed Point Theorem

**Theorem 3.2 (Kleene):**
Let f : D → D be continuous on CPO D.
Then f has a least fixed point:
```
fix(f) = ⊔ᵢ fⁱ(⊥)

where:
  f⁰(⊥) = ⊥
  fⁱ⁺¹(⊥) = f(fⁱ(⊥))
```

**Proof:**
```
1. Chain: ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ ...
   (by monotonicity and ⊥ ⊑ f(⊥))

2. Let d = ⊔ᵢ fⁱ(⊥)

3. d is a fixed point:
   f(d) = f(⊔ᵢ fⁱ(⊥))
        = ⊔ᵢ f(fⁱ(⊥))        (continuity)
        = ⊔ᵢ fⁱ⁺¹(⊥)
        = ⊔ᵢ fⁱ(⊥)           (shift index)
        = d

4. d is least:
   Let f(e) = e.
   Claim: ∀i. fⁱ(⊥) ⊑ e
   Base: ⊥ ⊑ e ✓
   Step: fⁱ(⊥) ⊑ e → fⁱ⁺¹(⊥) = f(fⁱ(⊥)) ⊑ f(e) = e ✓

   So d = ⊔ᵢ fⁱ(⊥) ⊑ e
∎
```

### 3.3 Application to Phronesis

**Observation:** Phronesis doesn't need fixed points because:
1. No recursive functions
2. No recursive types
3. All computations terminate

However, for future extensions (recursive types, iterators):
```
List(τ) ≅ μX. Unit + (τ × X)
Tree(τ) ≅ μX. τ + (X × X)
```

These would be solved as:
```
⟦μX.F(X)⟧ = fix(λD. ⟦F⟧[X ↦ D])
```

---

## 4. Scott Topology

### 4.1 Open Sets

**Definition 4.1 (Scott Open):**
U ⊆ D is Scott-open iff:
1. U is upward closed: x ∈ U ∧ x ⊑ y → y ∈ U
2. U is inaccessible by limits: ⊔ᵢ dᵢ ∈ U → ∃i. dᵢ ∈ U

### 4.2 Continuous = Topologically Continuous

**Theorem 4.1:** f : D → E is Scott-continuous iff f is topologically continuous w.r.t. Scott topologies.

**Proof:**
```
(→) Let V be Scott-open in E.
    Show f⁻¹(V) is Scott-open in D.

    1. Upward closed:
       d ∈ f⁻¹(V), d ⊑ d' → f(d) ⊑ f(d') (monotone)
       f(d) ∈ V, V upward closed → f(d') ∈ V
       → d' ∈ f⁻¹(V) ✓

    2. Inaccessible:
       ⊔ᵢ dᵢ ∈ f⁻¹(V) → f(⊔ᵢ dᵢ) ∈ V
       → ⊔ᵢ f(dᵢ) ∈ V (continuity)
       → ∃i. f(dᵢ) ∈ V (V inaccessible)
       → ∃i. dᵢ ∈ f⁻¹(V) ✓

(←) Topological continuity implies order-theoretic continuity
    (standard argument)
∎
```

---

## 5. Domain Constructors

### 5.1 Lifting

**Definition 5.1:**
```
D_⊥ = D ⊎ {⊥}

with ⊥ ⊑ d for all d
     d ⊑ d' iff d = d' (for d, d' ∈ D)
```

**Theorem 5.1:** If D is a CPO, so is D_⊥.

### 5.2 Product

**Definition 5.2:**
```
D × E = {(d, e) | d ∈ D, e ∈ E}
(d₁, e₁) ⊑ (d₂, e₂) iff d₁ ⊑ d₂ ∧ e₁ ⊑ e₂
⊥_{D×E} = (⊥_D, ⊥_E)
```

**Theorem 5.2:** D × E is a CPO if D and E are.

### 5.3 Function Space

**Definition 5.3:**
```
[D → E] = {f : D → E | f is continuous}
f ⊑ g iff ∀d. f(d) ⊑ g(d)
⊥_{[D→E]} = λd. ⊥_E
```

**Theorem 5.3:** [D → E] is a CPO if D and E are.

**Proof:**
```
Let (fᵢ) be a chain in [D → E].
Define g = λd. ⊔ᵢ fᵢ(d)

1. g is well-defined: (fᵢ(d)) is a chain for each d.

2. g is continuous:
   g(⊔ⱼ dⱼ) = ⊔ᵢ fᵢ(⊔ⱼ dⱼ)
             = ⊔ᵢ ⊔ⱼ fᵢ(dⱼ)    (each fᵢ continuous)
             = ⊔ⱼ ⊔ᵢ fᵢ(dⱼ)    (interchange)
             = ⊔ⱼ g(dⱼ)

3. g = ⊔ᵢ fᵢ: straightforward
∎
```

### 5.4 Sum

**Definition 5.4:**
```
D + E = {⊥} ∪ {inl(d) | d ∈ D \ {⊥}} ∪ {inr(e) | e ∈ E \ {⊥}}

Ordering:
  ⊥ ⊑ x for all x
  inl(d) ⊑ inl(d') iff d ⊑ d'
  inr(e) ⊑ inr(e') iff e ⊑ e'
```

---

## 6. Bilimits and Recursive Domains

### 6.1 Embedding-Projection Pairs

**Definition 6.1:**
(e, p) : D ◁ E is an embedding-projection pair iff:
```
e : D → E is continuous
p : E → D is continuous
p ∘ e = id_D
e ∘ p ⊑ id_E
```

### 6.2 Category of Domains

**Definition 6.2:**
**Dom** is the category where:
- Objects: CPOs
- Morphisms: Continuous functions
- Composition: Function composition
- Identity: id

### 6.3 Bilimits

**Theorem 6.1:** Dom has all bilimits (inverse limits).

Given a sequence:
```
D₀ ◁^{e₀,p₀} D₁ ◁^{e₁,p₁} D₂ ◁ ...
```

The bilimit is:
```
D_∞ = {(d₀, d₁, d₂, ...) | ∀i. pᵢ(dᵢ₊₁) = dᵢ}
```

### 6.4 Solving Recursive Domain Equations

**Theorem 6.2:** For continuous functor F : Dom → Dom,
the equation D ≅ F(D) has a solution.

**Method:**
```
D₀ = 1 (terminal object)
Dᵢ₊₁ = F(Dᵢ)
D_∞ = bilim Dᵢ
```

---

## 7. Phronesis Domains

### 7.1 Base Type Domains

```
⟦Int⟧ = ℤ_⊥         (flat integers with bottom)
⟦Float⟧ = ℝ_⊥       (flat reals with bottom)
⟦Bool⟧ = {⊥, tt, ff}
⟦String⟧ = Σ*_⊥
⟦Null⟧ = {⊥, ★}
```

### 7.2 Constructed Domains

```
⟦List(τ)⟧ = (⟦τ⟧*)_⊥
⟦Record{l₁:τ₁,...}⟧ = ⟦τ₁⟧ × ... × ⟦τₙ⟧
⟦τ₁ → τ₂⟧ = [⟦τ₁⟧ → ⟦τ₂⟧]
```

### 7.3 Simplification for Total Language

Since Phronesis is total (always terminates):
- We don't need ⊥ to represent non-termination
- Can use simpler set-theoretic semantics
- CPO structure still useful for:
  - Abstract interpretation
  - Partial evaluation
  - Future extensions

---

## 8. Adequacy Theorem

### 8.1 Logical Relations

**Definition 8.1:**
Define relation ~_τ between values and domain elements:
```
n ~_Int d    iff d = n
b ~_Bool d   iff d = b
vs ~_List(τ) d iff d = [v₁,...,vₙ] ∧ ∀i. vᵢ ~_τ dᵢ
```

### 8.2 Fundamental Theorem

**Theorem 8.1 (Adequacy):**
If Γ ⊢ e : τ and ρ ~_Γ η, then:
```
ρ ⊢ e ⇓ v ⟺ ⟦e⟧η = d ∧ v ~_τ d
```

**Proof:** By induction on typing derivation.

*Case literals:* Immediate from definitions.

*Case variables:*
```
⟦x⟧η = η(x)
ρ ⊢ x ⇓ ρ(x)
ρ(x) ~_τ η(x) by assumption
∎
```

*Case binary operations:* Use IH on subexpressions.

---

## 9. Computational Adequacy

### 9.1 Statement

**Theorem 9.1 (Computational Adequacy):**
```
⟦e⟧ρ ≠ ⊥ ⟺ e terminates
```

### 9.2 For Phronesis

Since all Phronesis programs terminate:
```
∀e. ⟦e⟧ρ ≠ ⊥
```

This is a corollary of the termination theorem.

---

## 10. Full Abstraction

### 10.1 Contextual Equivalence

**Definition 10.1:**
```
e₁ ≃_ctx e₂ iff ∀C. C[e₁]⇓ ⟺ C[e₂]⇓
```

### 10.2 Denotational Equivalence

**Definition 10.2:**
```
e₁ ≃_den e₂ iff ⟦e₁⟧ = ⟦e₂⟧
```

### 10.3 Full Abstraction

**Theorem 10.1:**
For Phronesis:
```
e₁ ≃_ctx e₂ ⟺ e₁ ≃_den e₂
```

**Proof Sketch:**
- Soundness (⟸): Compositionality of denotations
- Completeness (⟹): All functions in domains are definable (due to simple type system)

---

## 11. Summary

| Concept | Definition | Use in Phronesis |
|---------|------------|------------------|
| CPO | Poset with chain lubs | Semantic domains |
| Continuity | Preserves chain lubs | Function semantics |
| Fixed Point | ⊔ᵢ fⁱ(⊥) | (Future: recursion) |
| Scott Topology | Open = upward + inaccessible | Topological semantics |
| Bilimit | Inverse limit | Recursive types |
| Adequacy | ⇓ ↔ ⟦⟧ ≠ ⊥ | Semantic correctness |

---

## References

1. Amadio, R. M., & Curien, P.-L. (1998). *Domains and Lambda-Calculi*. Cambridge.
2. Abramsky, S., & Jung, A. (1994). *Domain Theory*. Handbook of Logic in CS.
3. Gunter, C. A. (1992). *Semantics of Programming Languages*. MIT Press.
4. Winskel, G. (1993). *The Formal Semantics of Programming Languages*. MIT Press.
