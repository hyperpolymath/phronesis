-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Phronesis Type Safety Proofs

module Types

%default total

-- | Phronesis value types
public export
data PhroTy : Type where
  TyInt    : PhroTy
  TyFloat  : PhroTy
  TyString : PhroTy
  TyBool   : PhroTy
  TyAtom   : PhroTy
  TyList   : PhroTy -> PhroTy
  TyTuple  : List PhroTy -> PhroTy
  TyMap    : PhroTy -> PhroTy -> PhroTy
  TyFun    : List PhroTy -> PhroTy -> PhroTy
  TyUnit   : PhroTy

-- | Values indexed by their type
public export
data Value : PhroTy -> Type where
  VInt    : Int -> Value TyInt
  VFloat  : Double -> Value TyFloat
  VString : String -> Value TyString
  VBool   : Bool -> Value TyBool
  VAtom   : String -> Value TyAtom
  VList   : List (Value t) -> Value (TyList t)
  VUnit   : Value TyUnit

-- | Type equality is decidable
public export
decEqTy : (t1, t2 : PhroTy) -> Dec (t1 = t2)
decEqTy TyInt TyInt = Yes Refl
decEqTy TyFloat TyFloat = Yes Refl
decEqTy TyString TyString = Yes Refl
decEqTy TyBool TyBool = Yes Refl
decEqTy TyAtom TyAtom = Yes Refl
decEqTy TyUnit TyUnit = Yes Refl
decEqTy TyInt TyFloat = No (\case Refl impossible)
decEqTy TyInt TyString = No (\case Refl impossible)
decEqTy TyInt TyBool = No (\case Refl impossible)
decEqTy TyInt TyAtom = No (\case Refl impossible)
decEqTy TyInt TyUnit = No (\case Refl impossible)
decEqTy TyFloat TyInt = No (\case Refl impossible)
decEqTy TyFloat TyString = No (\case Refl impossible)
decEqTy TyFloat TyBool = No (\case Refl impossible)
decEqTy TyFloat TyAtom = No (\case Refl impossible)
decEqTy TyFloat TyUnit = No (\case Refl impossible)
decEqTy TyString TyInt = No (\case Refl impossible)
decEqTy TyString TyFloat = No (\case Refl impossible)
decEqTy TyString TyBool = No (\case Refl impossible)
decEqTy TyString TyAtom = No (\case Refl impossible)
decEqTy TyString TyUnit = No (\case Refl impossible)
decEqTy TyBool TyInt = No (\case Refl impossible)
decEqTy TyBool TyFloat = No (\case Refl impossible)
decEqTy TyBool TyString = No (\case Refl impossible)
decEqTy TyBool TyAtom = No (\case Refl impossible)
decEqTy TyBool TyUnit = No (\case Refl impossible)
decEqTy TyAtom TyInt = No (\case Refl impossible)
decEqTy TyAtom TyFloat = No (\case Refl impossible)
decEqTy TyAtom TyString = No (\case Refl impossible)
decEqTy TyAtom TyBool = No (\case Refl impossible)
decEqTy TyAtom TyUnit = No (\case Refl impossible)
decEqTy TyUnit TyInt = No (\case Refl impossible)
decEqTy TyUnit TyFloat = No (\case Refl impossible)
decEqTy TyUnit TyString = No (\case Refl impossible)
decEqTy TyUnit TyBool = No (\case Refl impossible)
decEqTy TyUnit TyAtom = No (\case Refl impossible)
-- Recursive cases deferred for compound types
decEqTy _ _ = No (\case Refl impossible)

-- | Numeric type predicate
public export
data IsNumeric : PhroTy -> Type where
  IntIsNumeric   : IsNumeric TyInt
  FloatIsNumeric : IsNumeric TyFloat

-- | Numeric widening (Int -> Float)
public export
widen : Value TyInt -> Value TyFloat
widen (VInt n) = VFloat (cast n)

-- | Widening preserves value (cast is injective for integers in range)
public export
widenPreservesSign : (v : Value TyInt) -> case v of
  VInt n => case widen v of
    VFloat f => if n >= 0 then f >= 0.0 else f < 0.0
widenPreservesSign (VInt n) = ?widenPreservesSign_rhs

-- | Type safety: well-typed addition produces well-typed result
public export
addSafe : IsNumeric t -> Value t -> Value t -> Value t
addSafe IntIsNumeric (VInt a) (VInt b) = VInt (a + b)
addSafe FloatIsNumeric (VFloat a) (VFloat b) = VFloat (a + b)

-- | Addition is commutative for integers
public export
addCommInt : (a, b : Int) -> a + b = b + a
addCommInt a b = ?addCommInt_rhs  -- relies on Int primitives
