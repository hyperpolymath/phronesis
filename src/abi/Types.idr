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

-- | Type equality is decidable.
--
-- Compound types (TyList, TyTuple, TyMap, TyFun) are decided structurally,
-- mutually with the field-list decider `decEqTys`. Every same-head case is
-- handled explicitly, so the final catch-all sees only distinct-head pairs and
-- `Refl impossible` is genuinely valid there. (The earlier version punted ALL
-- compound cases to that catch-all, which is unsound: `TyList a = TyList b` is
-- inhabited by `Refl` when `a = b`.)
public export
decEqTys : (xs, ys : List PhroTy) -> Dec (xs = ys)

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
-- recursive (compound) diagonal cases, via constructor injectivity
decEqTy (TyList a) (TyList b) = case decEqTy a b of
  Yes Refl => Yes Refl
  No contra => No (\case Refl => contra Refl)
decEqTy (TyTuple xs) (TyTuple ys) = case decEqTys xs ys of
  Yes Refl => Yes Refl
  No contra => No (\case Refl => contra Refl)
decEqTy (TyMap a b) (TyMap c d) = case decEqTy a c of
  Yes Refl => case decEqTy b d of
    Yes Refl => Yes Refl
    No contra => No (\case Refl => contra Refl)
  No contra => No (\case Refl => contra Refl)
decEqTy (TyFun args1 ret1) (TyFun args2 ret2) = case decEqTys args1 args2 of
  Yes Refl => case decEqTy ret1 ret2 of
    Yes Refl => Yes Refl
    No contra => No (\case Refl => contra Refl)
  No contra => No (\case Refl => contra Refl)
-- remaining off-diagonal pairs involving a compound head (all distinct heads,
-- hence genuinely absurd). Enumerated because Idris will not accept `Refl
-- impossible` under a wildcard `_ _` catch-all.
decEqTy TyInt (TyList _) = No (\case Refl impossible)
decEqTy TyInt (TyTuple _) = No (\case Refl impossible)
decEqTy TyInt (TyMap _ _) = No (\case Refl impossible)
decEqTy TyInt (TyFun _ _) = No (\case Refl impossible)
decEqTy TyFloat (TyList _) = No (\case Refl impossible)
decEqTy TyFloat (TyTuple _) = No (\case Refl impossible)
decEqTy TyFloat (TyMap _ _) = No (\case Refl impossible)
decEqTy TyFloat (TyFun _ _) = No (\case Refl impossible)
decEqTy TyString (TyList _) = No (\case Refl impossible)
decEqTy TyString (TyTuple _) = No (\case Refl impossible)
decEqTy TyString (TyMap _ _) = No (\case Refl impossible)
decEqTy TyString (TyFun _ _) = No (\case Refl impossible)
decEqTy TyBool (TyList _) = No (\case Refl impossible)
decEqTy TyBool (TyTuple _) = No (\case Refl impossible)
decEqTy TyBool (TyMap _ _) = No (\case Refl impossible)
decEqTy TyBool (TyFun _ _) = No (\case Refl impossible)
decEqTy TyAtom (TyList _) = No (\case Refl impossible)
decEqTy TyAtom (TyTuple _) = No (\case Refl impossible)
decEqTy TyAtom (TyMap _ _) = No (\case Refl impossible)
decEqTy TyAtom (TyFun _ _) = No (\case Refl impossible)
decEqTy TyUnit (TyList _) = No (\case Refl impossible)
decEqTy TyUnit (TyTuple _) = No (\case Refl impossible)
decEqTy TyUnit (TyMap _ _) = No (\case Refl impossible)
decEqTy TyUnit (TyFun _ _) = No (\case Refl impossible)
decEqTy (TyList _) TyInt = No (\case Refl impossible)
decEqTy (TyList _) TyFloat = No (\case Refl impossible)
decEqTy (TyList _) TyString = No (\case Refl impossible)
decEqTy (TyList _) TyBool = No (\case Refl impossible)
decEqTy (TyList _) TyAtom = No (\case Refl impossible)
decEqTy (TyList _) TyUnit = No (\case Refl impossible)
decEqTy (TyList _) (TyTuple _) = No (\case Refl impossible)
decEqTy (TyList _) (TyMap _ _) = No (\case Refl impossible)
decEqTy (TyList _) (TyFun _ _) = No (\case Refl impossible)
decEqTy (TyTuple _) TyInt = No (\case Refl impossible)
decEqTy (TyTuple _) TyFloat = No (\case Refl impossible)
decEqTy (TyTuple _) TyString = No (\case Refl impossible)
decEqTy (TyTuple _) TyBool = No (\case Refl impossible)
decEqTy (TyTuple _) TyAtom = No (\case Refl impossible)
decEqTy (TyTuple _) TyUnit = No (\case Refl impossible)
decEqTy (TyTuple _) (TyList _) = No (\case Refl impossible)
decEqTy (TyTuple _) (TyMap _ _) = No (\case Refl impossible)
decEqTy (TyTuple _) (TyFun _ _) = No (\case Refl impossible)
decEqTy (TyMap _ _) TyInt = No (\case Refl impossible)
decEqTy (TyMap _ _) TyFloat = No (\case Refl impossible)
decEqTy (TyMap _ _) TyString = No (\case Refl impossible)
decEqTy (TyMap _ _) TyBool = No (\case Refl impossible)
decEqTy (TyMap _ _) TyAtom = No (\case Refl impossible)
decEqTy (TyMap _ _) TyUnit = No (\case Refl impossible)
decEqTy (TyMap _ _) (TyList _) = No (\case Refl impossible)
decEqTy (TyMap _ _) (TyTuple _) = No (\case Refl impossible)
decEqTy (TyMap _ _) (TyFun _ _) = No (\case Refl impossible)
decEqTy (TyFun _ _) TyInt = No (\case Refl impossible)
decEqTy (TyFun _ _) TyFloat = No (\case Refl impossible)
decEqTy (TyFun _ _) TyString = No (\case Refl impossible)
decEqTy (TyFun _ _) TyBool = No (\case Refl impossible)
decEqTy (TyFun _ _) TyAtom = No (\case Refl impossible)
decEqTy (TyFun _ _) TyUnit = No (\case Refl impossible)
decEqTy (TyFun _ _) (TyList _) = No (\case Refl impossible)
decEqTy (TyFun _ _) (TyTuple _) = No (\case Refl impossible)
decEqTy (TyFun _ _) (TyMap _ _) = No (\case Refl impossible)

decEqTys [] [] = Yes Refl
decEqTys [] (_ :: _) = No (\case Refl impossible)
decEqTys (_ :: _) [] = No (\case Refl impossible)
decEqTys (x :: xs) (y :: ys) = case decEqTy x y of
  Yes Refl => case decEqTys xs ys of
    Yes Refl => Yes Refl
    No contra => No (\case Refl => contra Refl)
  No contra => No (\case Refl => contra Refl)

-- | Numeric type predicate
public export
data IsNumeric : PhroTy -> Type where
  IntIsNumeric   : IsNumeric TyInt
  FloatIsNumeric : IsNumeric TyFloat

-- | Numeric widening (Int -> Float)
public export
widen : Value TyInt -> Value TyFloat
widen (VInt n) = VFloat (cast n)

-- | Type safety: well-typed addition produces well-typed result
public export
addSafe : IsNumeric t -> Value t -> Value t -> Value t
addSafe IntIsNumeric (VInt a) (VInt b) = VInt (a + b)
addSafe FloatIsNumeric (VFloat a) (VFloat b) = VFloat (a + b)
