-- SPDX-License-Identifier: MPL-2.0
-- SPDX-License-Identifier: CC-BY-SA-4.0
-- Copyright (c) 2026 Jonathan D.A. Jewell
--
-- =====================================================================
-- PhronesisEcho — echo-types integrated into Phronesis's semantics
-- =====================================================================
--
-- Phronesis is a provably-safe language for *agentic ethical reasoning*.
-- Its evaluator `eval : Env Γ → Expr Γ τ → ⟦ τ ⟧` is, like any decision
-- procedure, generally NON-INJECTIVE: many distinct situations (closed
-- expressions) collapse to the same verdict.  That collapse is exactly the
-- information an auditor of an ethical decision needs back.
--
-- hyperpolymath/echo-types provides the canonical, mechanised form of that
-- retained loss — the fiber `Echo f y := Σ A (λ x → f x ≡ y)`.  Specialised
-- to the verdict map, `Echo verdict v` is the *provenance* of verdict `v`:
-- the proof-relevant record of which expressions justify it.  A non-injective
-- verdict map has more than one provenance for a verdict, and (by the same
-- no-section argument echo-types makes elsewhere) the verdict alone cannot
-- recover which one fired.  This module pins that correspondence so the
-- language's semantics and the echo-types formalisation share ONE notion of
-- structured loss.
--
-- Flag stance: left at Agda's default discipline (matching Phronesis.agda),
-- importing the `--safe --without-K` `Echo`.  Machine-checked against the real
-- echo-types library (registered as `echo-types`); see phronesis-formal.agda-lib.

module PhronesisEcho where

open import Echo using (Echo; echo-intro)
open import Phronesis
  using ( PhrType; TBool; ∅; Expr; bool; _∧ᵉ_; Env; ε; eval )

open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)


-- =====================================================================
-- § 1. The verdict map: closed boolean evaluation as a classifier.
-- =====================================================================
--
-- A closed boolean Phronesis expression (a policy condition over the empty
-- context) evaluates to a Bool verdict.  This is the lossy classifier whose
-- Echo carries the provenance.

verdict : Expr ∅ TBool → Bool
verdict = eval ε

-- The provenance of a verdict: which closed expressions justify it.
Provenance : Bool → Set
Provenance v = Echo verdict v


-- =====================================================================
-- § 2. A verdict has many provenances (the loss is real and retained).
-- =====================================================================
--
-- Two genuinely different closed expressions both justify the verdict `true`;
-- their Echoes are distinct provenance witnesses over the same verdict.

reason-a : Expr ∅ TBool
reason-a = bool true

reason-b : Expr ∅ TBool
reason-b = bool true ∧ᵉ bool true

-- Each is a provenance of `true` (echo-intro lands each in its own fiber,
-- because `verdict reason-a ≡ true` and `verdict reason-b ≡ true`).
provenance-a : Provenance true
provenance-a = echo-intro verdict reason-a

provenance-b : Provenance true
provenance-b = echo-intro verdict reason-b

-- The two justifications are distinct expressions (a literal vs a conjunction).
reasons-distinct : reason-a ≢ reason-b
reasons-distinct ()

-- HEADLINE: the verdict map is non-injective — the verdict `true` does NOT
-- determine its provenance.  `Echo verdict true` is the object that retains,
-- and `proj₁` recovers, *which* expression justified the decision; the verdict
-- in `⟦ TBool ⟧ = Bool` has forgotten it.  This is the type-level statement
-- that an ethical verdict is auditable only with its echo, not on its own.
verdict-forgets-provenance :
  Σ (Expr ∅ TBool) (λ a → Σ (Expr ∅ TBool) (λ b →
    (verdict a ≡ verdict b) × (a ≢ b)))
verdict-forgets-provenance = reason-a , reason-b , refl , reasons-distinct

-- The Echo retains what the verdict drops: each provenance reproduces its
-- source expression under proj₁.
provenance-recovers-source-a : proj₁ provenance-a ≡ reason-a
provenance-recovers-source-a = refl

provenance-recovers-source-b : proj₁ provenance-b ≡ reason-b
provenance-recovers-source-b = refl
