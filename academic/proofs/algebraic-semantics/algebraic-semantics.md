# Algebraic Semantics for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides algebraic semantics for Phronesis using initial algebras, F-algebras, and universal algebra, enabling compositional reasoning about program structure.

---

## 1. Many-Sorted Algebra

### 1.1 Signature

**Definition 1.1 (Signature):**
```
Σ = (S, Ω)

where:
  S = set of sorts (types)
  Ω = family of operation symbols
      Ωₛ₁...ₛₙ,ₛ = operations with args s₁,...,sₙ returning s
```

### 1.2 Phronesis Signature

```
Sorts S = {Int, Bool, String, IP, List, Record, Action, Policy, Expr, Type}

Operations Ω:
  -- Constants
  zero : → Int
  succ : Int → Int
  true, false : → Bool

  -- Arithmetic
  add, sub, mul, div : Int × Int → Int

  -- Boolean
  and, or : Bool × Bool → Bool
  not : Bool → Bool

  -- Comparison
  eq : τ × τ → Bool  (polymorphic family)
  lt, le, gt, ge : Int × Int → Bool

  -- Constructors
  nil : → List(τ)
  cons : τ × List(τ) → List(τ)
  empty : → Record
  extend : Record × Field × τ → Record

  -- Actions
  accept, reject : String → Action
  report : String → Action
  continue : → Action

  -- Policy
  policy : String × Expr × Action × Action × Int → Policy
```

### 1.3 Σ-Algebra

**Definition 1.2:**
A Σ-algebra A consists of:
```
- Carrier sets Aₛ for each sort s ∈ S
- Functions fᴬ : Aₛ₁ × ... × Aₛₙ → Aₛ for each f ∈ Ωₛ₁...ₛₙ,ₛ
```

**Phronesis Standard Interpretation:**
```
A_Int = ℤ
A_Bool = {⊤, ⊥}
A_String = Σ*
A_IP = {0, ..., 2³²-1} × {0, ..., 32}
A_List(τ) = List(Aτ)
A_Action = {Accept(s), Reject(s), Report(s), Continue | s ∈ A_String}
```

---

## 2. Term Algebra

### 2.1 Definition

**Definition 2.1 (Term Algebra):**
```
T_Σ(X) = terms built from:
  - Variables x ∈ X
  - Constants c ∈ Ω₋,ₛ
  - Applications f(t₁, ..., tₙ) for f ∈ Ωₛ₁...ₛₙ,ₛ, tᵢ ∈ T_Σ(X)ₛᵢ
```

### 2.2 Ground Terms

**Definition 2.2:**
```
T_Σ = T_Σ(∅) = closed terms (no variables)
```

### 2.3 Term Structure

**Example Terms:**
```
add(succ(zero), succ(succ(zero)))        -- 1 + 2
and(true, not(false))                     -- true ∧ ¬false
cons(zero, cons(succ(zero), nil))         -- [0, 1]
policy("p", cond, accept("ok"), reject("no"), 100)
```

---

## 3. Initial Algebra

### 3.1 Definition

**Definition 3.1 (Initial Algebra):**
A Σ-algebra I is initial iff for every Σ-algebra A, there exists a unique homomorphism !: I → A.

```
        I
        |
    !   ↓  unique
        A
```

### 3.2 Initiality of Term Algebra

**Theorem 3.1:** T_Σ is the initial Σ-algebra.

**Proof:**
For any Σ-algebra A, define the unique homomorphism eval: T_Σ → A:
```
eval(c) = cᴬ                           for constants
eval(f(t₁,...,tₙ)) = fᴬ(eval(t₁),...,eval(tₙ))
```

Uniqueness: Any homomorphism must satisfy these equations.
Existence: The recursion is well-founded on term structure. ∎

### 3.3 Semantic Function

**Definition 3.3:**
The unique homomorphism !: T_Σ → A gives the semantics:
```
⟦·⟧ : T_Σ → A
⟦t⟧ = !(t)
```

---

## 4. F-Algebras

### 4.1 Definition

**Definition 4.1 (F-Algebra):**
For functor F: C → C, an F-algebra is a pair (A, α) where:
```
A ∈ Ob(C)           -- carrier object
α : F(A) → A        -- structure map
```

### 4.2 Expression Functor

**Definition 4.2:**
```
ExprF(X) = Int
         + Bool
         + String
         + X × X                    -- binary ops
         + X                        -- unary ops
         + X × X × X                -- if-then-else
         + List(X)                  -- list literal
         + Map(Field, X)            -- record literal
```

### 4.3 Initial F-Algebra

**Theorem 4.1:** The initial F-algebra for ExprF is:
```
(Expr, in) where Expr = μX. ExprF(X)
in : ExprF(Expr) → Expr
```

### 4.4 Catamorphism (Fold)

**Definition 4.3:**
For F-algebra (A, α), the unique morphism from initial algebra:
```
⦇α⦈ : μF → A

such that:
⦇α⦈ ∘ in = α ∘ F(⦇α⦈)
```

**Diagram:**
```
F(μF) --F(⦇α⦈)--> F(A)
  |                 |
  in                α
  ↓                 ↓
  μF ---⦇α⦈----->   A
```

### 4.5 Phronesis Evaluation as Catamorphism

```
evalAlg : ExprF(Val) → Val
evalAlg(Inl n) = n                           -- Int literal
evalAlg(Inr (Inl b)) = b                     -- Bool literal
evalAlg(Inr (Inr (Inl s))) = s               -- String literal
evalAlg(Inr (Inr (Inr (Inl (v1, v2))))) =    -- Binary op
  case op of Add → v1 + v2, ...
evalAlg(Inr (Inr (Inr (Inr (...))))) = ...   -- Other cases

eval = ⦇evalAlg⦈ : Expr → Val
```

---

## 5. Anamorphism (Unfold)

### 5.1 F-Coalgebra

**Definition 5.1:**
An F-coalgebra is (A, α) with α : A → F(A).

### 5.2 Final Coalgebra

**Definition 5.2:**
The final F-coalgebra νF has unique morphism from any coalgebra:
```
[(α)] : A → νF
```

### 5.3 Anamorphism

```
F(A) <--F([(α)])-- F(νF)
  ↑                  ↑
  α                  out
  |                  |
  A ---[(α)]--->    νF
```

### 5.4 Stream Generation

**Example:** Generating infinite sequence of consensus rounds:
```
roundCoalg : State → RoundF(State)
roundCoalg(s) = (current_epoch(s), next_state(s))

rounds = [(roundCoalg)] : State → Stream(Round)
```

---

## 6. Hylomorphism

### 6.1 Definition

**Definition 6.1:**
Hylomorphism combines unfold then fold:
```
⟦α, γ⟧ = ⦇α⦈ ∘ [(γ)]

A --[(γ)]--> μF --⦇α⦈--> B
```

### 6.2 Deforestation

**Theorem 6.1:**
Hylomorphism can be computed without building intermediate structure:
```
⟦α, γ⟧ = hylo(α, γ)

hylo(α, γ)(a) = α(F(hylo(α, γ))(γ(a)))
```

### 6.3 Example: Policy Evaluation

```
-- Unfold: parse policy chain
parseCoalg : String → PolicyChainF(String)

-- Fold: evaluate policy chain
evalAlg : PolicyChainF(Result) → Result

-- Combined without intermediate AST:
evaluatePolicy = ⟦evalAlg, parseCoalg⟧
```

---

## 7. Equational Logic

### 7.1 Equations

**Definition 7.1:**
An equation over Σ is t₁ = t₂ where t₁, t₂ ∈ T_Σ(X).

### 7.2 Phronesis Axioms

```
-- Arithmetic
add(x, zero) = x
add(x, succ(y)) = succ(add(x, y))
mul(x, zero) = zero
mul(x, succ(y)) = add(mul(x, y), x)

-- Boolean
and(x, true) = x
and(x, false) = false
or(x, true) = true
or(x, false) = x
not(not(x)) = x

-- List
append(nil, ys) = ys
append(cons(x, xs), ys) = cons(x, append(xs, ys))

-- Conditional
if(true, x, y) = x
if(false, x, y) = y
```

### 7.3 Equational Deduction

**Rules:**
```
──────────── [Refl]
  t = t

  t₁ = t₂
──────────── [Sym]
  t₂ = t₁

t₁ = t₂    t₂ = t₃
─────────────────── [Trans]
     t₁ = t₃

     t₁ = t₂
────────────────────────── [Cong]
f(...,t₁,...) = f(...,t₂,...)

        t₁ = t₂
────────────────────── [Subst]
t₁[s/x] = t₂[s/x]
```

---

## 8. Quotient Algebra

### 8.1 Congruence

**Definition 8.1:**
≡ is a congruence on Σ-algebra A iff:
```
∀f ∈ Ω, ∀a₁ ≡ a₁', ..., aₙ ≡ aₙ':
  fᴬ(a₁,...,aₙ) ≡ fᴬ(a₁',...,aₙ')
```

### 8.2 Quotient

**Definition 8.2:**
A/≡ is the quotient algebra with:
```
[a]_≡ ∈ (A/≡)ₛ for a ∈ Aₛ
fᴬ/≡([a₁],...,[aₙ]) = [fᴬ(a₁,...,aₙ)]
```

### 8.3 Application: Type Equivalence

```
Type equivalence ~ on types:
  List(Int) ~ List(Int)
  Record{a: Int, b: Bool} ~ Record{b: Bool, a: Int}  (field order)

Types/~ gives canonical type representatives.
```

---

## 9. Free Algebra

### 9.1 Definition

**Definition 9.1:**
F_Σ(X) is the free Σ-algebra over set X iff:
```
For any Σ-algebra A and function f: X → |A|,
there exists unique homomorphism f̄: F_Σ(X) → A extending f.
```

### 9.2 Construction

**Theorem 9.1:** F_Σ(X) = T_Σ(X), the term algebra with variables.

### 9.3 Substitution as Homomorphism

```
σ : Var → T_Σ(Var)  defines substitution

σ̄ : T_Σ(Var) → T_Σ(Var) is the unique extension

t[σ] = σ̄(t)
```

---

## 10. Abstract Data Types

### 10.1 Specification

**Definition 10.1:**
ADT specification (Σ, E) consists of:
```
Σ = signature
E = set of equations
```

### 10.2 Phronesis IP Prefix ADT

```
ADT IPPrefix:
  Signature:
    ip : Int → Int → Int → Int → Int → IP  -- a.b.c.d/n
    contains : IP × IP → Bool
    aggregate : IP × IP → Maybe(IP)

  Equations:
    contains(ip(a,b,c,d,n), ip(a',b',c',d',m)) =
      m >= n AND prefix_match(a.b.c.d, a'.b'.c'.d', n)

    aggregate(ip₁, ip₂) = Some(ip₃) iff
      adjacent(ip₁, ip₂) AND same_length(ip₁, ip₂)
```

### 10.3 Model Existence

**Theorem 10.1:**
Every specification (Σ, E) has an initial model: T_Σ/≡_E.

---

## 11. Module Algebra

### 11.1 Parameterized Modules

**Definition 11.1:**
```
MODULE M[P : SPEC] : SPEC' =
  ... implementation using P ...
```

### 11.2 Module Composition

```
M₁ + M₂    -- Module sum
M₁ × M₂    -- Module product
M₁[M₂]     -- Module instantiation
```

### 11.3 Phronesis Policy Module

```
MODULE PolicyEngine[R : RouteSpec] : PolicySpec =
  TYPE Policy = ...
  FUN evaluate : Route → Policy → Result
  FUN chain : List(Policy) → Route → Result

  AXIOM:
    chain([], r) = Accept
    chain(p::ps, r) =
      case evaluate(r, p) of
        Continue → chain(ps, r)
        result → result
```

---

## 12. Coalgebraic Semantics

### 12.1 Behavioral Equivalence

**Definition 12.1:**
Two states s₁, s₂ are behaviorally equivalent (s₁ ∼ s₂) iff they cannot be distinguished by observations.

### 12.2 Bisimulation

**Definition 12.2:**
R is a bisimulation on F-coalgebra (A, α) iff:
```
R ⊆ A × A
(a₁, a₂) ∈ R → α(a₁) ∼_F α(a₂)  (related by F-lifting of R)
```

### 12.3 Coinduction Principle

**Theorem 12.1:**
If R is a bisimulation, then ∀(a₁, a₂) ∈ R. a₁ ∼ a₂.

### 12.4 Consensus State Equivalence

```
Two consensus states are equivalent iff:
  - Same committed log prefix
  - Same current epoch
  - Equivalent pending proposals

Bisimulation proof shows equivalence is preserved by transitions.
```

---

## 13. Rewriting Systems

### 13.1 Term Rewriting

**Definition 13.1:**
Rewrite rule: l → r where l, r ∈ T_Σ(X), Var(r) ⊆ Var(l).

### 13.2 Phronesis Reduction Rules

```
-- β-reduction for conditionals
IF true THEN e₁ ELSE e₂ → e₁
IF false THEN e₁ ELSE e₂ → e₂

-- Arithmetic simplification
0 + e → e
e + 0 → e
e - 0 → e
1 * e → e
e * 1 → e
e * 0 → 0

-- Boolean simplification
true AND e → e
false AND e → false
true OR e → true
false OR e → e
NOT (NOT e) → e
```

### 13.3 Confluence

**Theorem 13.1:** Phronesis rewriting is confluent.

**Proof:** By Newman's lemma (local confluence + termination → confluence). Local confluence by case analysis. Termination by decreasing term size. ∎

### 13.4 Normalization

**Definition 13.2:**
Normal form: term with no applicable rewrite rules.

**Theorem 13.2:** Every Phronesis term has a unique normal form.

---

## 14. Categorical Semantics

### 14.1 Cartesian Closed Category

```
Objects: Phronesis types
Morphisms: Type-preserving functions

Products: τ₁ × τ₂
Exponentials: τ₁ → τ₂
Terminal: Unit
```

### 14.2 Interpretation

```
⟦τ₁ × τ₂⟧ = ⟦τ₁⟧ × ⟦τ₂⟧
⟦τ₁ → τ₂⟧ = ⟦τ₁⟧ → ⟦τ₂⟧
⟦List(τ)⟧ = μX. 1 + ⟦τ⟧ × X
```

---

## 15. Summary

| Concept | Application |
|---------|-------------|
| Signature | Type and operation specification |
| Term Algebra | AST representation |
| Initial Algebra | Unique interpretation |
| F-Algebra | Recursive data types |
| Catamorphism | Generic fold (evaluation) |
| Anamorphism | Generic unfold (generation) |
| Equations | Semantic equivalence |
| Free Algebra | Substitution |
| ADT | Module specification |
| Coalgebra | Infinite/reactive behavior |
| Rewriting | Normalization |

---

## References

1. Goguen, J., et al. (1977). *Initial Algebra Semantics and Continuous Algebras*. JACM.
2. Meijer, E., et al. (1991). *Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire*. FPCA.
3. Jacobs, B. (2016). *Introduction to Coalgebra*. Cambridge.
4. Baader, F., & Nipkow, T. (1998). *Term Rewriting and All That*. Cambridge.
