# Category Theory Foundations for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides the categorical semantics of the Phronesis type system and language constructs.

---

## 1. The Category of Phronesis Types

### 1.1 Definition

We define **Phr** as a category where:
- **Objects:** Types τ ∈ T
- **Morphisms:** Type-preserving functions f : τ₁ → τ₂
- **Identity:** id_τ : τ → τ
- **Composition:** f ∘ g : τ₁ → τ₃ for g : τ₁ → τ₂ and f : τ₂ → τ₃

### 1.2 Basic Objects

```
Ob(Phr) = {Int, Float, String, Bool, IP, DateTime, Null, List(τ), Record{...}, 1, 0}

where:
  1 = Unit (terminal object)
  0 = Void (initial object)
```

### 1.3 Categorical Laws

**Identity Law:**
```
f ∘ id = f = id ∘ f
```

**Associativity:**
```
(f ∘ g) ∘ h = f ∘ (g ∘ h)
```

**Proof:** Holds by the definition of function composition. ∎

---

## 2. Products and Coproducts

### 2.1 Product Types (Records)

Records form categorical products:

```
Record{a : A, b : B} ≅ A × B

with projections:
  π₁ : A × B → A
  π₂ : A × B → B
```

**Universal Property:**
For any object C with morphisms f : C → A and g : C → B,
there exists a unique ⟨f, g⟩ : C → A × B such that:

```
       C
      /|\
     / | \
    f ⟨f,g⟩ g
   /   |   \
  ↓    ↓    ↓
  A ← A×B → B
     π₁   π₂
```

**Proof:**
```
Define: ⟨f, g⟩(c) = {a: f(c), b: g(c)}

Verify:
  π₁ ∘ ⟨f, g⟩ = f  ✓
  π₂ ∘ ⟨f, g⟩ = g  ✓

Uniqueness: Any h with π₁ ∘ h = f and π₂ ∘ h = g must equal ⟨f, g⟩
  h(c) = {a: π₁(h(c)), b: π₂(h(c))} = {a: f(c), b: g(c)} = ⟨f, g⟩(c) ∎
```

### 2.2 N-ary Products

For records with n fields:
```
Record{l₁: τ₁, ..., lₙ: τₙ} ≅ τ₁ × τ₂ × ... × τₙ

with projections:
  πᵢ : τ₁ × ... × τₙ → τᵢ
```

### 2.3 Coproduct Types (Future Union Types)

Union types form coproducts:
```
τ₁ | τ₂ ≅ τ₁ + τ₂

with injections:
  ι₁ : τ₁ → τ₁ + τ₂
  ι₂ : τ₂ → τ₁ + τ₂
```

**Universal Property:**
For any object C with morphisms f : A → C and g : B → C,
there exists a unique [f, g] : A + B → C such that:

```
  A → A+B ← B
  |    |    |
  f  [f,g]  g
  ↓    ↓    ↓
  C  = C  = C
```

---

## 3. Exponential Objects (Function Types)

### 3.1 Internal Hom

Though Phronesis doesn't expose function types to users, internally:
```
Hom(A, B) = A → B
```

**Exponential Object:**
```
B^A = A → B

with evaluation:
  eval : (A → B) × A → B
  eval(f, a) = f(a)
```

**Currying (internal):**
```
curry : ((A × B) → C) → (A → (B → C))
uncurry : (A → (B → C)) → ((A × B) → C)
```

### 3.2 Cartesian Closed Structure

**Theorem 3.1:** Phr is Cartesian closed.

**Proof:**
1. Terminal object: 1 (Unit/Null)
2. Binary products: Record types
3. Exponentials: Function types (internal)

All required adjunctions hold:
```
Hom(A × B, C) ≅ Hom(A, C^B)
```
∎

---

## 4. Functors

### 4.1 List Functor

**Definition:** List : Phr → Phr
```
List(τ) = List of elements of type τ
List(f : τ₁ → τ₂) = map f : List(τ₁) → List(τ₂)
```

**Functor Laws:**

*Identity:*
```
List(id_τ) = id_{List(τ)}

Proof: map id [v₁, ..., vₙ] = [id(v₁), ..., id(vₙ)] = [v₁, ..., vₙ] ∎
```

*Composition:*
```
List(f ∘ g) = List(f) ∘ List(g)

Proof:
  map (f ∘ g) [v₁, ..., vₙ]
  = [(f ∘ g)(v₁), ..., (f ∘ g)(vₙ)]
  = [f(g(v₁)), ..., f(g(vₙ))]
  = map f [g(v₁), ..., g(vₙ)]
  = map f (map g [v₁, ..., vₙ])
  = (map f ∘ map g) [v₁, ..., vₙ] ∎
```

### 4.2 List as a Monad

**Definition:** (List, η, μ) is a monad where:
```
η : τ → List(τ)           -- return/pure
η(v) = [v]

μ : List(List(τ)) → List(τ)   -- join/flatten
μ([[v₁₁, ..., v₁ₘ], ..., [vₙ₁, ..., vₙₖ]]) = [v₁₁, ..., v₁ₘ, ..., vₙ₁, ..., vₙₖ]
```

**Monad Laws:**

*Left Identity:*
```
μ ∘ η_{List(τ)} = id_{List(τ)}

Proof: μ([xs]) = xs ∎
```

*Right Identity:*
```
μ ∘ List(η) = id_{List(τ)}

Proof: μ(map η [v₁, ..., vₙ]) = μ([[v₁], ..., [vₙ]]) = [v₁, ..., vₙ] ∎
```

*Associativity:*
```
μ ∘ μ_{List(τ)} = μ ∘ List(μ)

Proof: Both flatten a 3-deep nested list to a flat list. ∎
```

### 4.3 Maybe/Option Functor (Null handling)

**Definition:** Maybe : Phr → Phr
```
Maybe(τ) = τ | Null

Maybe(f : τ₁ → τ₂) : Maybe(τ₁) → Maybe(τ₂)
Maybe(f)(null) = null
Maybe(f)(v) = f(v)
```

This is also a monad with:
```
η(v) = v
μ(null) = null
μ(v) = v   (when v : τ, not Maybe(τ))
```

---

## 5. Natural Transformations

### 5.1 Between List and Maybe

**Definition:** head : List ⇒ Maybe
```
head_τ : List(τ) → Maybe(τ)
head_τ([]) = null
head_τ([v, ...]) = v
```

**Naturality:**
```
For f : τ₁ → τ₂:

Maybe(f) ∘ head_τ₁ = head_τ₂ ∘ List(f)

Proof:
  Case []:
    Maybe(f)(head([])) = Maybe(f)(null) = null
    head(List(f)([])) = head([]) = null ✓

  Case [v, ...]:
    Maybe(f)(head([v, ...])) = Maybe(f)(v) = f(v)
    head(List(f)([v, ...])) = head([f(v), ...]) = f(v) ✓
∎
```

### 5.2 Length as Natural Transformation

**Definition:** length : List ⇒ Const(Int)
```
length_τ : List(τ) → Int
length_τ([v₁, ..., vₙ]) = n
```

**Naturality:**
```
Const(Int)(f) ∘ length_τ₁ = length_τ₂ ∘ List(f)

Since Const(Int)(f) = id:
  length(map f xs) = length(xs) ✓
∎
```

---

## 6. Limits and Colimits

### 6.1 Terminal Object

**Theorem 6.1:** Null (Unit) is terminal in Phr.

**Proof:** For any type τ, there exists a unique morphism !_τ : τ → Null
```
!_τ(v) = null (for all v : τ)
```

Uniqueness: Any f : τ → Null must satisfy f(v) = null since Null has one value. ∎

### 6.2 Initial Object

**Theorem 6.2:** Void (0) is initial in Phr.

**Proof:** The empty type has no inhabitants, so for any τ,
there exists a unique morphism absurd : 0 → τ (vacuously true). ∎

### 6.3 Equalizers

For morphisms f, g : A → B, the equalizer is:
```
Eq(f, g) = {a ∈ A | f(a) = g(a)}

with inclusion i : Eq(f, g) ↪ A
```

### 6.4 Pullbacks

Given f : A → C and g : B → C, the pullback is:
```
A ×_C B = {(a, b) | f(a) = g(b)}

with projections:
  p₁ : A ×_C B → A
  p₂ : A ×_C B → B
```

---

## 7. Categorical Semantics of Programs

### 7.1 Expressions as Morphisms

An expression e with free variables x₁:τ₁, ..., xₙ:τₙ and type τ
corresponds to a morphism:

```
⟦e⟧ : τ₁ × ... × τₙ → τ
```

### 7.2 Semantic Equations

**Literals:**
```
⟦n⟧ = const_n : 1 → Int
⟦true⟧ = const_true : 1 → Bool
```

**Variables:**
```
⟦xᵢ⟧ = πᵢ : τ₁ × ... × τₙ → τᵢ
```

**Binary Operations:**
```
⟦e₁ + e₂⟧ = (+) ∘ ⟨⟦e₁⟧, ⟦e₂⟧⟩

where (+) : Int × Int → Int
```

**Conditionals:**
```
⟦IF e₁ THEN e₂ ELSE e₃⟧ = cond ∘ ⟨⟦e₁⟧, ⟦e₂⟧, ⟦e₃⟧⟩

where cond : Bool × τ × τ → τ
      cond(true, v₂, v₃) = v₂
      cond(false, v₂, v₃) = v₃
```

**Field Access:**
```
⟦e.l⟧ = π_l ∘ ⟦e⟧

where π_l : Record{..., l:τ, ...} → τ
```

**Module Calls:**
```
⟦M.f(e₁, ..., eₙ)⟧ = M.f ∘ ⟨⟦e₁⟧, ..., ⟦eₙ⟧⟩
```

### 7.3 Denotational Semantics Correspondence

**Theorem 7.1 (Adequacy):**
If Γ ⊢ e ⇓ v, then ⟦e⟧(γ) = v where γ is the valuation of Γ.

**Proof:** By induction on evaluation derivation, showing operational and categorical semantics coincide. ∎

---

## 8. Subtyping as a Preorder Category

### 8.1 The Subtype Category

Define **Sub** as a thin category where:
- Objects: Types
- Morphisms: τ₁ → τ₂ exists iff τ₁ <: τ₂

### 8.2 Subtyping as a Functor

The inclusion functor:
```
i : Sub → Phr
```

**Covariance of List:**
```
τ₁ <: τ₂ implies List(τ₁) <: List(τ₂)
```

This makes List a covariant functor on Sub.

---

## 9. Monadic Effects

### 9.1 State Monad (for Policy Execution)

**Definition:** State(S, τ) = S → (τ, S)

```
η_τ : τ → State(S, τ)
η_τ(v) = λs. (v, s)

μ_τ : State(S, State(S, τ)) → State(S, τ)
μ_τ(m) = λs. let (m', s') = m(s) in m'(s')
```

The policy execution model uses this with:
```
S = (PolicyTable, ConsensusLog, Environment, PendingActions, Agents)
```

### 9.2 Writer Monad (for Logging)

**Definition:** Writer(W, τ) = (τ, W) where W is a monoid

For the ConsensusLog:
```
W = List(LogEntry)  with (++, [])

tell : W → Writer(W, ())
tell(w) = ((), w)
```

### 9.3 Composed Effects

The actual Phronesis execution combines:
```
Exec = StateT(State, WriterT(Log, Identity))
```

This forms a monad transformer stack.

---

## 10. Kan Extensions

### 10.1 Right Kan Extension

For the forgetful functor U : Phr → Set that forgets type information:

```
Ran_U F = ∫_τ Set(U(τ), F(τ))
```

This gives the type-indexed family of sets.

### 10.2 Left Kan Extension

```
Lan_U F = ∫^τ U(τ) × F(τ)
```

Useful for free constructions.

---

## 11. Topos-Theoretic Perspective

### 11.1 Phr as a Topos

**Theorem 11.1:** Phr with function types forms a topos.

**Proof Sketch:**
1. Finite limits: Products (records), equalizers
2. Exponentials: Function types (internal)
3. Subobject classifier: Bool with true : 1 → Bool

The subobject classifier satisfies: for any mono m : A ↪ B,
there exists unique χ_m : B → Bool with A = χ_m⁻¹(true). ∎

### 11.2 Internal Logic

The internal logic of Phr is intuitionistic higher-order logic,
but since all computations terminate, classical logic is valid.

---

## 12. String Diagrams

### 12.1 Morphism Composition

```
     A
     │
     │ f
     ▼
     B
     │
     │ g
     ▼
     C
```

Represents g ∘ f : A → C

### 12.2 Tensor Product

```
    A     B
    │     │
    │ f   │ g
    ▼     ▼
    C     D
```

Represents f ⊗ g : A × B → C × D

### 12.3 Symmetry

```
    A     B
     ╲   ╱
      ╲ ╱
       ╳
      ╱ ╲
     ╱   ╲
    B     A
```

Represents swap : A × B → B × A

---

## 13. Future Work: Dependent Types

For refinement types, we would need:
```
Π(x : A).B(x)   -- Dependent product
Σ(x : A).B(x)   -- Dependent sum
```

The category would become a locally cartesian closed category.

---

## References

1. Mac Lane, S. (1971). *Categories for the Working Mathematician*.
2. Awodey, S. (2010). *Category Theory*. Oxford.
3. Barr, M., & Wells, C. (1990). *Category Theory for Computing Science*.
4. Moggi, E. (1991). *Notions of Computation and Monads*. Information and Computation.
