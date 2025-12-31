# Set-Theoretic Foundations for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides rigorous set-theoretic foundations for Phronesis, establishing the mathematical basis for type theory, semantics, and formal verification.

---

## 1. Axiomatic Set Theory (ZFC)

### 1.1 ZFC Axioms

**Axiom 1.1 (Extensionality):**
```
∀A, B. (∀x. x ∈ A ↔ x ∈ B) → A = B
```

**Axiom 1.2 (Empty Set):**
```
∃∅. ∀x. x ∉ ∅
```

**Axiom 1.3 (Pairing):**
```
∀a, b. ∃P. ∀x. x ∈ P ↔ (x = a ∨ x = b)
```

**Axiom 1.4 (Union):**
```
∀A. ∃U. ∀x. x ∈ U ↔ ∃Y. Y ∈ A ∧ x ∈ Y
```

**Axiom 1.5 (Power Set):**
```
∀A. ∃P. ∀x. x ∈ P ↔ x ⊆ A
```

**Axiom 1.6 (Infinity):**
```
∃I. ∅ ∈ I ∧ (∀x. x ∈ I → x ∪ {x} ∈ I)
```

**Axiom 1.7 (Separation/Specification):**
```
∀A, φ. ∃B. ∀x. x ∈ B ↔ (x ∈ A ∧ φ(x))
```

**Axiom 1.8 (Replacement):**
```
∀A, F. (∀x ∈ A. ∃!y. F(x,y)) → ∃B. ∀y. y ∈ B ↔ ∃x ∈ A. F(x,y)
```

**Axiom 1.9 (Foundation/Regularity):**
```
∀A ≠ ∅. ∃x ∈ A. x ∩ A = ∅
```

**Axiom 1.10 (Choice):**
```
∀A. (∅ ∉ A) → ∃f: A → ∪A. ∀X ∈ A. f(X) ∈ X
```

---

## 2. Type Universes

### 2.1 Cumulative Hierarchy

**Definition 2.1:**
```
V₀ = ∅
Vₐ₊₁ = P(Vₐ)
Vₗ = ∪{Vₐ | α < λ}  for limit λ
V = ∪{Vₐ | α ∈ Ord}
```

### 2.2 Rank Function

**Definition 2.2:**
```
rank(x) = min{α | x ∈ Vₐ₊₁}
        = sup{rank(y) + 1 | y ∈ x}
```

### 2.3 Universe Levels in Phronesis

**Definition 2.3:**
```
Type₀ = base types {Int, Bool, String, ...}
Type₁ = Type₀ ∪ {τ₁ → τ₂ | τ₁, τ₂ ∈ Type₀} ∪ {List(τ) | τ ∈ Type₀}
Typeₙ₊₁ = Typeₙ ∪ constructors over Typeₙ
```

---

## 3. Relations and Functions

### 3.1 Ordered Pairs

**Definition 3.1 (Kuratowski):**
```
(a, b) = {{a}, {a, b}}

Properties:
  (a, b) = (c, d) ↔ a = c ∧ b = d
```

### 3.2 Cartesian Product

**Definition 3.2:**
```
A × B = {(a, b) | a ∈ A ∧ b ∈ B}
```

### 3.3 Relations

**Definition 3.3:**
```
R ⊆ A × B is a relation from A to B

dom(R) = {a | ∃b. (a, b) ∈ R}
ran(R) = {b | ∃a. (a, b) ∈ R}
```

### 3.4 Functions

**Definition 3.4:**
```
f: A → B is a function iff:
  f ⊆ A × B
  ∀a ∈ A. ∃!b ∈ B. (a, b) ∈ f

Notation: f(a) = b when (a, b) ∈ f
```

### 3.5 Phronesis Functions

**Semantic Function:**
```
⟦·⟧ : Expr → (Env → Val)
⟦·⟧ ∈ P(Expr × (Env → Val))
```

---

## 4. Cardinals

### 4.1 Cardinality

**Definition 4.1:**
```
|A| = |B| ⟺ ∃f: A ↔ B (bijection)
|A| ≤ |B| ⟺ ∃f: A → B (injection)
|A| < |B| ⟺ |A| ≤ |B| ∧ |A| ≠ |B|
```

### 4.2 Cardinal Arithmetic

**Definition 4.2:**
```
|A| + |B| = |A ⊎ B|           (disjoint union)
|A| × |B| = |A × B|           (Cartesian product)
|A|^|B| = |A^B| = |{f: B → A}|  (function space)
```

### 4.3 Phronesis Cardinalities

```
|IPv4| = 2³²
|IPv6| = 2¹²⁸
|AS_paths of length ≤ L| = Σₖ₌₀^L |ASN|^k = (|ASN|^(L+1) - 1)/(|ASN| - 1)
|Types| = ℵ₀ (countably infinite with recursive types)
```

---

## 5. Ordinals

### 5.1 Definition

**Definition 5.1:**
```
α is an ordinal iff α is transitive and well-ordered by ∈

Transitive: ∀x ∈ α. x ⊆ α
Well-ordered: ∈ is a well-order on α
```

### 5.2 Ordinal Arithmetic

**Definition 5.2:**
```
0 = ∅
α + 1 = α ∪ {α}
α + β = ∪{α + γ | γ < β}  (limit case)
α · β = type of α × β with lexicographic order
α^β = type of functions β → α with Cantor ordering
```

### 5.3 Transfinite Induction

**Theorem 5.1:**
For property P over ordinals:
```
(∀α. (∀β < α. P(β)) → P(α)) → ∀α. P(α)
```

### 5.4 Application to Termination

**Theorem 5.2:**
Phronesis expressions have ordinal rank bounded by ω.
```
rank(literal) = 0
rank(e₁ op e₂) = max(rank(e₁), rank(e₂)) + 1
rank(IF c THEN e₁ ELSE e₂) = max(rank(c), rank(e₁), rank(e₂)) + 1
```

---

## 6. Inductively Defined Sets

### 6.1 Definition Schema

**Definition 6.1:**
Given rules R = {(premises, conclusion)}, the inductively defined set I(R) is the least set closed under R:
```
I(R) = ∩{S | S closed under R}
```

### 6.2 Phronesis Type Induction

**Rules for Types:**
```
───────── [T-Int]
Int ∈ Type

───────── [T-Bool]
Bool ∈ Type

───────── [T-String]
String ∈ Type

τ ∈ Type
─────────────── [T-List]
List(τ) ∈ Type

{fᵢ : τᵢ}ᵢ, τᵢ ∈ Type
────────────────────────── [T-Record]
Record{f₁: τ₁, ...} ∈ Type
```

### 6.3 Induction Principle

**Theorem 6.1:**
To prove P(τ) for all τ ∈ Type:
1. Prove P(Int), P(Bool), P(String)
2. Assume P(τ), prove P(List(τ))
3. Assume P(τᵢ) for all i, prove P(Record{...})

---

## 7. Fixed Point Theory

### 7.1 Monotone Functions on P(X)

**Definition 7.1:**
F: P(X) → P(X) is monotone iff:
```
A ⊆ B → F(A) ⊆ F(B)
```

### 7.2 Knaster-Tarski

**Theorem 7.1:**
For monotone F on complete lattice (P(X), ⊆):
```
lfp(F) = ∩{S | F(S) ⊆ S} = ∪{S | S ⊆ F(S)}
gfp(F) = ∪{S | S ⊆ F(S)} = ∩{S | F(S) ⊆ S}
```

### 7.3 Recursive Type Definition

**Definition 7.2:**
For type equation τ = F(τ):
```
Least solution: τ = lfp(F) (finite/inductive types)
Greatest solution: τ = gfp(F) (infinite/coinductive types)
```

---

## 8. Well-Founded Relations

### 8.1 Definition

**Definition 8.1:**
R ⊆ A × A is well-founded iff:
```
∀S ⊆ A. S ≠ ∅ → ∃m ∈ S. ∀x ∈ S. ¬(x R m)
```

### 8.2 Well-Founded Recursion

**Theorem 8.1:**
For well-founded R and function step:
```
∃!f. ∀x. f(x) = step(x, λy. (y R x) → f(y))
```

### 8.3 Application

**Expression Evaluation:**
```
R = strict subexpression relation (well-founded)
eval(e) = case e of
  literal → value
  e₁ op e₂ → eval(e₁) op eval(e₂)  (e₁ R e, e₂ R e)
  ...
```

---

## 9. Quotient Sets

### 9.1 Equivalence Relations

**Definition 9.1:**
R ⊆ A × A is an equivalence relation iff:
```
Reflexive: ∀x. x R x
Symmetric: x R y → y R x
Transitive: x R y ∧ y R z → x R z
```

### 9.2 Quotient

**Definition 9.2:**
```
A/R = {[a]_R | a ∈ A}
where [a]_R = {b ∈ A | a R b}
```

### 9.3 Type Equivalence

**Definition 9.3:**
```
τ₁ ≡ τ₂ ⟺ τ₁ <: τ₂ ∧ τ₂ <: τ₁

Types/≡ = canonical type representatives
```

---

## 10. Partial Orders as Sets

### 10.1 Order-Theoretic Sets

**Definition 10.1:**
```
(P, ≤) represented as:
  P = carrier set
  ≤ ⊆ P × P with order properties
```

### 10.2 Type Lattice

**Definition 10.2:**
```
Types = {Int, Bool, String, List(...), Record{...}, Any, Never, ...}
<: ⊆ Types × Types
  where τ₁ <: τ₂ ⟺ "τ₁ is subtype of τ₂"

(Types, <:) forms bounded lattice:
  ⊥ = Never
  ⊤ = Any
```

---

## 11. Category-Theoretic Sets

### 11.1 Set as Category

**Definition 11.1:**
Set is the category:
```
Objects: Sets
Morphisms: Functions
Composition: Function composition
Identity: id_A : A → A
```

### 11.2 Limits and Colimits

**Definition 11.2:**
```
Product: A × B with projections π₁, π₂
Coproduct: A + B with injections ι₁, ι₂
Equalizer: eq(f, g) = {x | f(x) = g(x)}
Pullback: A ×_C B = {(a,b) | f(a) = g(b)}
```

### 11.3 Phronesis Categorical Constructs

```
Record types = products
Sum types = coproducts
List(τ) = initial algebra of X ↦ 1 + τ × X
```

---

## 12. Multisets

### 12.1 Definition

**Definition 12.1:**
```
Multiset over A: M : A → ℕ
M(a) = multiplicity of a in M

Operations:
  M₁ ⊎ M₂ : (M₁ ⊎ M₂)(a) = M₁(a) + M₂(a)
  M₁ ∩ M₂ : (M₁ ∩ M₂)(a) = min(M₁(a), M₂(a))
  M₁ ⊆ M₂ : ∀a. M₁(a) ≤ M₂(a)
```

### 12.2 Application: Vote Counting

```
Votes : Agent → ℕ  (multiset of votes)
Votes(APPROVE) = count of approval votes
Votes(REJECT) = count of rejection votes

threshold_met ⟺ Votes(APPROVE) ≥ t
```

---

## 13. Indexed Families

### 13.1 Definition

**Definition 13.1:**
```
Indexed family: {Aᵢ}ᵢ∈I = function A : I → V
Aᵢ = A(i)
```

### 13.2 Dependent Products and Sums

**Definition 13.2:**
```
Πᵢ∈I Aᵢ = {f : I → ∪Aᵢ | ∀i. f(i) ∈ Aᵢ}
Σᵢ∈I Aᵢ = {(i, a) | i ∈ I ∧ a ∈ Aᵢ}
```

### 13.3 Application: Agent States

```
States : Agent → StateType
States(i) = current state of agent i

∀i ∈ Agents. States(i) ∈ {Idle, Voting, Waiting, ...}
```

---

## 14. Boolean Algebras

### 14.1 Definition

**Definition 14.1:**
Boolean algebra (B, ∧, ∨, ¬, 0, 1) satisfies:
```
x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)   (distributivity)
x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z)
x ∧ ¬x = 0                         (complement)
x ∨ ¬x = 1
```

### 14.2 Boolean Expressions

**Theorem 14.1:**
Phronesis Boolean expressions form a Boolean algebra.
```
B = {Phronesis Bool expressions}/≡
Operations: AND, OR, NOT
Identity: true, false
```

---

## 15. Model Theory Connection

### 15.1 Structures

**Definition 15.1:**
A structure M for signature Σ:
```
M = (|M|, {f^M}, {R^M})

|M| = universe (carrier set)
f^M : |M|^n → |M| for n-ary function symbol f
R^M ⊆ |M|^n for n-ary relation symbol R
```

### 15.2 Phronesis as Structure

```
Phronesis Structure M:
  |M| = Val (set of values)
  +^M : ℤ × ℤ → ℤ (integer addition)
  AND^M : 𝔹 × 𝔹 → 𝔹 (boolean and)
  IN^M ⊆ Val × List(Val) (membership)
  <:^M ⊆ Type × Type (subtyping)
```

---

## 16. Summary

| Set-Theoretic Concept | Phronesis Application |
|-----------------------|----------------------|
| ZFC Axioms | Foundation for all mathematics |
| Cumulative Hierarchy | Universe levels |
| Cardinals | Size of type domains |
| Ordinals | Termination measures |
| Inductive Sets | Type definitions |
| Fixed Points | Recursive types |
| Well-Founded | Evaluation termination |
| Quotients | Type equivalence |
| Partial Orders | Type lattice |
| Multisets | Vote counting |

---

## References

1. Kunen, K. (2011). *Set Theory*. College Publications.
2. Jech, T. (2003). *Set Theory: The Third Millennium Edition*. Springer.
3. Enderton, H. B. (1977). *Elements of Set Theory*. Academic Press.
4. Halmos, P. R. (1960). *Naive Set Theory*. Van Nostrand.
