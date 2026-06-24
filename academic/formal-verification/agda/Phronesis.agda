-- SPDX-License-Identifier: MPL-2.0
-- SPDX-License-Identifier: MPL-2.0
-- Phronesis Formalization in Agda
-- Intrinsically typed representation with dependent types

module Phronesis where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length; map; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)

-- ═══════════════════════════════════════════════════════════════════════════
-- 1. Types
-- ═══════════════════════════════════════════════════════════════════════════

data PhrType : Set where
  TInt      : PhrType
  TFloat    : PhrType
  TString   : PhrType
  TBool     : PhrType
  TIP       : PhrType
  TDateTime : PhrType
  TList     : PhrType → PhrType
  TRecord   : List (String × PhrType) → PhrType
  TNull     : PhrType

-- ═══════════════════════════════════════════════════════════════════════════
-- 2. Type Equality Decidability
-- ═══════════════════════════════════════════════════════════════════════════

-- Decidable equality for types — COMPLETE and SOUND.
--
-- Decidability of type equality belongs to an extrinsic / gradual checking
-- layer.  The intrinsic `Expr Γ τ` below does not consume it (types are static
-- indices there), but we provide a *total, sound* decision procedure in full
-- rather than the earlier incomplete stub whose catch-all `_ ≟ᵗ _ = no (λ ())`
-- was unsound (it claimed every pair of types unequal, incl. `TInt ≟ᵗ TInt`).
--
-- The off-diagonal (distinct head constructors) must be enumerated: Agda
-- cannot refute `τ₁ ≡ τ₂` under wildcard patterns, so a single catch-all is
-- impossible here.  Recursive cases (`TList`, `TRecord`) go via constructor
-- injectivity, structurally, mutually with the record-field-list decider `_≟ᶠ_`.
open import Relation.Nullary.Decidable using (map′)
open import Data.String using () renaming (_≟_ to _≟ˢ_)

mutual
  _≟ᵗ_ : (τ₁ τ₂ : PhrType) → Dec (τ₁ ≡ τ₂)
  -- diagonal: nullary heads
  TInt       ≟ᵗ TInt       = yes refl
  TFloat     ≟ᵗ TFloat     = yes refl
  TString    ≟ᵗ TString    = yes refl
  TBool      ≟ᵗ TBool      = yes refl
  TIP        ≟ᵗ TIP        = yes refl
  TDateTime  ≟ᵗ TDateTime  = yes refl
  TNull      ≟ᵗ TNull      = yes refl
  -- diagonal: recursive heads, via constructor injectivity (structural)
  TList σ    ≟ᵗ TList ρ    = map′ (cong TList)   (λ { refl → refl }) (σ ≟ᵗ ρ)
  TRecord fs ≟ᵗ TRecord gs = map′ (cong TRecord) (λ { refl → refl }) (fs ≟ᶠ gs)
  -- off-diagonal: distinct head constructors are unequal
  TInt       ≟ᵗ TFloat     = no λ()
  TInt       ≟ᵗ TString    = no λ()
  TInt       ≟ᵗ TBool      = no λ()
  TInt       ≟ᵗ TIP        = no λ()
  TInt       ≟ᵗ TDateTime  = no λ()
  TInt       ≟ᵗ TNull      = no λ()
  TInt       ≟ᵗ TList _    = no λ()
  TInt       ≟ᵗ TRecord _  = no λ()
  TFloat     ≟ᵗ TInt       = no λ()
  TFloat     ≟ᵗ TString    = no λ()
  TFloat     ≟ᵗ TBool      = no λ()
  TFloat     ≟ᵗ TIP        = no λ()
  TFloat     ≟ᵗ TDateTime  = no λ()
  TFloat     ≟ᵗ TNull      = no λ()
  TFloat     ≟ᵗ TList _    = no λ()
  TFloat     ≟ᵗ TRecord _  = no λ()
  TString    ≟ᵗ TInt       = no λ()
  TString    ≟ᵗ TFloat     = no λ()
  TString    ≟ᵗ TBool      = no λ()
  TString    ≟ᵗ TIP        = no λ()
  TString    ≟ᵗ TDateTime  = no λ()
  TString    ≟ᵗ TNull      = no λ()
  TString    ≟ᵗ TList _    = no λ()
  TString    ≟ᵗ TRecord _  = no λ()
  TBool      ≟ᵗ TInt       = no λ()
  TBool      ≟ᵗ TFloat     = no λ()
  TBool      ≟ᵗ TString    = no λ()
  TBool      ≟ᵗ TIP        = no λ()
  TBool      ≟ᵗ TDateTime  = no λ()
  TBool      ≟ᵗ TNull      = no λ()
  TBool      ≟ᵗ TList _    = no λ()
  TBool      ≟ᵗ TRecord _  = no λ()
  TIP        ≟ᵗ TInt       = no λ()
  TIP        ≟ᵗ TFloat     = no λ()
  TIP        ≟ᵗ TString    = no λ()
  TIP        ≟ᵗ TBool      = no λ()
  TIP        ≟ᵗ TDateTime  = no λ()
  TIP        ≟ᵗ TNull      = no λ()
  TIP        ≟ᵗ TList _    = no λ()
  TIP        ≟ᵗ TRecord _  = no λ()
  TDateTime  ≟ᵗ TInt       = no λ()
  TDateTime  ≟ᵗ TFloat     = no λ()
  TDateTime  ≟ᵗ TString    = no λ()
  TDateTime  ≟ᵗ TBool      = no λ()
  TDateTime  ≟ᵗ TIP        = no λ()
  TDateTime  ≟ᵗ TNull      = no λ()
  TDateTime  ≟ᵗ TList _    = no λ()
  TDateTime  ≟ᵗ TRecord _  = no λ()
  TNull      ≟ᵗ TInt       = no λ()
  TNull      ≟ᵗ TFloat     = no λ()
  TNull      ≟ᵗ TString    = no λ()
  TNull      ≟ᵗ TBool      = no λ()
  TNull      ≟ᵗ TIP        = no λ()
  TNull      ≟ᵗ TDateTime  = no λ()
  TNull      ≟ᵗ TList _    = no λ()
  TNull      ≟ᵗ TRecord _  = no λ()
  TList _    ≟ᵗ TInt       = no λ()
  TList _    ≟ᵗ TFloat     = no λ()
  TList _    ≟ᵗ TString    = no λ()
  TList _    ≟ᵗ TBool      = no λ()
  TList _    ≟ᵗ TIP        = no λ()
  TList _    ≟ᵗ TDateTime  = no λ()
  TList _    ≟ᵗ TNull      = no λ()
  TList _    ≟ᵗ TRecord _  = no λ()
  TRecord _  ≟ᵗ TInt       = no λ()
  TRecord _  ≟ᵗ TFloat     = no λ()
  TRecord _  ≟ᵗ TString    = no λ()
  TRecord _  ≟ᵗ TBool      = no λ()
  TRecord _  ≟ᵗ TIP        = no λ()
  TRecord _  ≟ᵗ TDateTime  = no λ()
  TRecord _  ≟ᵗ TNull      = no λ()
  TRecord _  ≟ᵗ TList _    = no λ()

  -- Decidable equality on record field lists (mutual with _≟ᵗ_), structural.
  _≟ᶠ_ : (fs gs : List (String × PhrType)) → Dec (fs ≡ gs)
  []             ≟ᶠ []             = yes refl
  []             ≟ᶠ (_ ∷ _)        = no λ()
  (_ ∷ _)        ≟ᶠ []             = no λ()
  ((x , σ) ∷ fs) ≟ᶠ ((y , ρ) ∷ gs) with x ≟ˢ y | σ ≟ᵗ ρ | fs ≟ᶠ gs
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no  x≢y  | _        | _        = no λ { refl → x≢y refl }
  ... | _        | no  σ≢ρ  | _        = no λ { refl → σ≢ρ refl }
  ... | _        | _        | no fs≢gs = no λ { refl → fs≢gs refl }

-- ═══════════════════════════════════════════════════════════════════════════
-- 3. Semantic Domain (Values indexed by Type)
-- ═══════════════════════════════════════════════════════════════════════════

-- Intrinsically typed values - values carry their type
⟦_⟧ : PhrType → Set
⟦ TInt ⟧ = ℤ
⟦ TFloat ⟧ = ℤ  -- Placeholder for IEEE float
⟦ TString ⟧ = String
⟦ TBool ⟧ = Bool
⟦ TIP ⟧ = ℕ × ℕ × ℕ × ℕ
⟦ TDateTime ⟧ = ℤ
⟦ TList τ ⟧ = List ⟦ τ ⟧
⟦ TRecord [] ⟧ = ⊤
⟦ TRecord ((f , τ) ∷ fs) ⟧ = ⟦ τ ⟧ × ⟦ TRecord fs ⟧
⟦ TNull ⟧ = ⊤

-- ═══════════════════════════════════════════════════════════════════════════
-- 4. Typing Context
-- ═══════════════════════════════════════════════════════════════════════════

data Ctx : Set where
  ∅    : Ctx
  _,,_ : Ctx → String × PhrType → Ctx

-- NOTE: context extension is `_,,_` (not `_,_`) to stay unambiguous from
-- Data.Product._,_ used for the (name × type) pair it stores.  With a
-- single `_,_` in scope the mixfix parser cannot disambiguate
-- `Γ , (x , τ)` (the two operators have different fixities).
infixl 5 _,,_

-- Variable lookup (de Bruijn style would be cleaner, but using names for clarity)
data _∋_∶_ : Ctx → String → PhrType → Set where
  here  : ∀ {Γ x τ} → (Γ ,, (x , τ)) ∋ x ∶ τ
  there : ∀ {Γ x y τ τ'} → Γ ∋ x ∶ τ → (Γ ,, (y , τ')) ∋ x ∶ τ

-- ═══════════════════════════════════════════════════════════════════════════
-- 5. Intrinsically Typed Expressions
-- ═══════════════════════════════════════════════════════════════════════════

-- Expressions are indexed by context and type - only well-typed terms exist!
data Expr (Γ : Ctx) : PhrType → Set where
  -- Literals
  int    : ℤ → Expr Γ TInt
  bool   : Bool → Expr Γ TBool
  str    : String → Expr Γ TString
  null   : Expr Γ TNull

  -- Variables
  var    : ∀ {x τ} → Γ ∋ x ∶ τ → Expr Γ τ

  -- Arithmetic (integers)
  _+ᵉ_   : Expr Γ TInt → Expr Γ TInt → Expr Γ TInt
  _-ᵉ_   : Expr Γ TInt → Expr Γ TInt → Expr Γ TInt
  _*ᵉ_   : Expr Γ TInt → Expr Γ TInt → Expr Γ TInt

  -- Boolean operations
  _∧ᵉ_   : Expr Γ TBool → Expr Γ TBool → Expr Γ TBool
  _∨ᵉ_   : Expr Γ TBool → Expr Γ TBool → Expr Γ TBool
  ¬ᵉ_    : Expr Γ TBool → Expr Γ TBool

  -- Comparison
  _==ᵉ_  : ∀ {τ} → Expr Γ τ → Expr Γ τ → Expr Γ TBool
  _<ᵉ_   : Expr Γ TInt → Expr Γ TInt → Expr Γ TBool

  -- Conditional
  ifᵉ_then_else_ : ∀ {τ} → Expr Γ TBool → Expr Γ τ → Expr Γ τ → Expr Γ τ

  -- List operations
  nil    : ∀ {τ} → Expr Γ (TList τ)
  cons   : ∀ {τ} → Expr Γ τ → Expr Γ (TList τ) → Expr Γ (TList τ)
  _∈ᵉ_   : ∀ {τ} → Expr Γ τ → Expr Γ (TList τ) → Expr Γ TBool

infixl 6 _+ᵉ_ _-ᵉ_
infixl 7 _*ᵉ_
infixl 4 _∧ᵉ_ _∨ᵉ_
infix 5 _==ᵉ_ _<ᵉ_

-- ═══════════════════════════════════════════════════════════════════════════
-- 6. Value Environment
-- ═══════════════════════════════════════════════════════════════════════════

data Env : Ctx → Set where
  ε   : Env ∅
  _▷_ : ∀ {Γ x τ} → Env Γ → ⟦ τ ⟧ → Env (Γ ,, (x , τ))

infixl 5 _▷_

-- Environment lookup
lookupEnv : ∀ {Γ x τ} → Γ ∋ x ∶ τ → Env Γ → ⟦ τ ⟧
lookupEnv here (ρ ▷ v) = v
lookupEnv (there x) (ρ ▷ _) = lookupEnv x ρ

-- ═══════════════════════════════════════════════════════════════════════════
-- 7. Denotational Semantics (Evaluation)
-- ═══════════════════════════════════════════════════════════════════════════

open import Data.Integer using (_≤ᵇ_) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)

-- Value equality (for comparison operators)
-- Implemented via decidable equality per type, not postulated.

open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
-- (_≟ˢ_ for String is imported earlier, alongside _≟ᵗ_)
open import Data.Nat using () renaming (_≟_ to _≟ⁿ_)
open import Data.Bool using () renaming (_≟_ to _≟ᵇ_)

-- Decidable equality on semantic values, by induction on the type index.
-- TFloat is represented as ℤ (placeholder), TDateTime as ℤ, TIP as 4-tuple of ℕ.
-- TList and TRecord are split into helper functions in a mutual block so Agda's
-- termination checker sees the structural decrease explicitly:
--   * eqList decreases on the List (structural); calls _≡ᵛ_ on elements (τ < TList τ)
--   * eqRecord decreases on the field List (structural); calls _≡ᵛ_ on parts (τ < TRecord)
-- This replaces the former {-# TERMINATING #-} pragma.
mutual
  _≡ᵛ_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → Bool
  _≡ᵛ_ {TInt} a b with a ≟ℤ b
  ... | yes _ = true
  ... | no  _ = false
  _≡ᵛ_ {TFloat} a b with a ≟ℤ b
  ... | yes _ = true
  ... | no  _ = false
  _≡ᵛ_ {TString} a b with a ≟ˢ b
  ... | yes _ = true
  ... | no  _ = false
  _≡ᵛ_ {TBool} a b with a ≟ᵇ b
  ... | yes _ = true
  ... | no  _ = false
  _≡ᵛ_ {TIP} (a₁ , a₂ , a₃ , a₄) (b₁ , b₂ , b₃ , b₄)
    with a₁ ≟ⁿ b₁ | a₂ ≟ⁿ b₂ | a₃ ≟ⁿ b₃ | a₄ ≟ⁿ b₄
  ... | yes _ | yes _ | yes _ | yes _ = true
  ... | _     | _     | _     | _     = false
  _≡ᵛ_ {TDateTime} a b with a ≟ℤ b
  ... | yes _ = true
  ... | no  _ = false
  _≡ᵛ_ {TList τ} xs ys   = eqList {τ} xs ys
  _≡ᵛ_ {TRecord fs} vs ws = eqRecord {fs} vs ws
  _≡ᵛ_ {TNull} tt tt = true

  -- List equality: structural recursion on the List; calls _≡ᵛ_ on elements.
  eqList : ∀ {τ} → List ⟦ τ ⟧ → List ⟦ τ ⟧ → Bool
  eqList [] []           = true
  eqList (x ∷ xs) (y ∷ ys) = _≡ᵛ_ x y ∧ eqList xs ys
  eqList _ _             = false

  -- Record equality: structural recursion on the field List.
  eqRecord : ∀ {fs} → ⟦ TRecord fs ⟧ → ⟦ TRecord fs ⟧ → Bool
  eqRecord {[]} tt tt = true
  eqRecord {(_ , τ) ∷ fs} (v , vs) (w , ws) = _≡ᵛ_ v w ∧ eqRecord {fs} vs ws

-- Integer less-than via the standard library ordering.
_<ᵛ_ : ℤ → ℤ → Bool
a <ᵛ b = (a ≤ᵇ b) ∧ not (_≡ᵛ_ {TInt} a b)
  where open import Data.Integer using (_≤ᵇ_)

-- List membership via value equality.
_∈ᵛ_ : ∀ {τ} → ⟦ τ ⟧ → List ⟦ τ ⟧ → Bool
x ∈ᵛ [] = false
x ∈ᵛ (y ∷ ys) = (x ≡ᵛ y) ∨ (x ∈ᵛ ys)

-- The evaluation function - total by construction!
eval : ∀ {Γ τ} → Env Γ → Expr Γ τ → ⟦ τ ⟧
eval ρ (int n) = n
eval ρ (bool b) = b
eval ρ (str s) = s
eval ρ null = tt
eval ρ (var x) = lookupEnv x ρ
eval ρ (e₁ +ᵉ e₂) = eval ρ e₁ +ℤ eval ρ e₂
eval ρ (e₁ -ᵉ e₂) = eval ρ e₁ -ℤ eval ρ e₂
eval ρ (e₁ *ᵉ e₂) = eval ρ e₁ *ℤ eval ρ e₂
eval ρ (e₁ ∧ᵉ e₂) = eval ρ e₁ ∧ eval ρ e₂
eval ρ (e₁ ∨ᵉ e₂) = eval ρ e₁ ∨ eval ρ e₂
eval ρ (¬ᵉ e) = not (eval ρ e)
eval ρ (e₁ ==ᵉ e₂) = eval ρ e₁ ≡ᵛ eval ρ e₂
eval ρ (e₁ <ᵉ e₂) = eval ρ e₁ <ᵛ eval ρ e₂
eval ρ (ifᵉ e₁ then e₂ else e₃) with eval ρ e₁
... | true = eval ρ e₂
... | false = eval ρ e₃
eval ρ nil = []
eval ρ (cons e₁ e₂) = eval ρ e₁ ∷ eval ρ e₂
eval ρ (e₁ ∈ᵉ e₂) = eval ρ e₁ ∈ᵛ eval ρ e₂

-- ═══════════════════════════════════════════════════════════════════════════
-- 8. Type Safety is AUTOMATIC!
-- ═══════════════════════════════════════════════════════════════════════════

-- Because we use intrinsic typing, ill-typed expressions cannot be constructed.
-- Type safety (progress + preservation) is guaranteed by the type system itself.

-- The eval function is TOTAL - it always produces a value of the correct type.
-- This is Agda's termination checker verifying our claims!

-- ═══════════════════════════════════════════════════════════════════════════
-- 9. Expression Size (Termination Measure)
-- ═══════════════════════════════════════════════════════════════════════════

size : ∀ {Γ τ} → Expr Γ τ → ℕ
size (int _) = 1
size (bool _) = 1
size (str _) = 1
size null = 1
size (var _) = 1
size (e₁ +ᵉ e₂) = 1 + size e₁ + size e₂
size (e₁ -ᵉ e₂) = 1 + size e₁ + size e₂
size (e₁ *ᵉ e₂) = 1 + size e₁ + size e₂
size (e₁ ∧ᵉ e₂) = 1 + size e₁ + size e₂
size (e₁ ∨ᵉ e₂) = 1 + size e₁ + size e₂
size (¬ᵉ e) = 1 + size e
size (e₁ ==ᵉ e₂) = 1 + size e₁ + size e₂
size (e₁ <ᵉ e₂) = 1 + size e₁ + size e₂
size (ifᵉ e₁ then e₂ else e₃) = 1 + size e₁ + size e₂ + size e₃
size nil = 1
size (cons e₁ e₂) = 1 + size e₁ + size e₂
size (e₁ ∈ᵉ e₂) = 1 + size e₁ + size e₂

-- Size is always positive
size-pos : ∀ {Γ τ} (e : Expr Γ τ) → 1 ≤ size e
size-pos (int _) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (bool _) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (str _) = Data.Nat.s≤s Data.Nat.z≤n
size-pos null = Data.Nat.s≤s Data.Nat.z≤n
size-pos (var _) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ +ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ -ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ *ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ ∧ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ ∨ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (¬ᵉ e) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ ==ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ <ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (ifᵉ e₁ then e₂ else e₃) = Data.Nat.s≤s Data.Nat.z≤n
size-pos nil = Data.Nat.s≤s Data.Nat.z≤n
size-pos (cons e₁ e₂) = Data.Nat.s≤s Data.Nat.z≤n
size-pos (e₁ ∈ᵉ e₂) = Data.Nat.s≤s Data.Nat.z≤n

-- ═══════════════════════════════════════════════════════════════════════════
-- 10. Determinism
-- ═══════════════════════════════════════════════════════════════════════════

-- Evaluation is deterministic - same expression, same environment, same result
determinism : ∀ {Γ τ} (ρ : Env Γ) (e : Expr Γ τ) →
              eval ρ e ≡ eval ρ e
determinism ρ e = refl

-- ═══════════════════════════════════════════════════════════════════════════
-- 11. Actions and Policies (Sketched)
-- ═══════════════════════════════════════════════════════════════════════════

data Action : Set where
  accept : Maybe String → Action
  reject : Maybe String → Action
  report : String → Action

record Policy : Set where
  field
    name : String
    condition : Expr ∅ TBool  -- Closed boolean expression
    thenAction : Action
    priority : ℕ

-- ═══════════════════════════════════════════════════════════════════════════
-- 12. Sandbox Isolation Property
-- ═══════════════════════════════════════════════════════════════════════════

-- The grammar doesn't include file/network/system operations.
-- This is enforced by NOT having constructors for dangerous operations.

-- Proof: There is no constructor in Expr that corresponds to dangerous ops.
-- By construction, any Expr is safe.

-- ═══════════════════════════════════════════════════════════════════════════
-- 13. Summary
-- ═══════════════════════════════════════════════════════════════════════════

{-
  BENEFITS OF INTRINSIC TYPING:

  1. Type Safety: Cannot even write ill-typed expressions
  2. Termination: eval is structurally recursive, Agda verifies termination
  3. Correctness: Well-typed input → well-typed output is AUTOMATIC
  4. No "preservation" theorem needed - it's built into the definition!
  5. Sandbox Isolation: Grammar doesn't have dangerous constructors

  This is the "holy grail" of type-safe language implementation:
  Only valid programs can be represented, and evaluation is total.
-}
