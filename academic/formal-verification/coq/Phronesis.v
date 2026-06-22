(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-License-Identifier: CC-BY-SA-4.0 *)
(* Phronesis Formalization in Coq *)
(* Complete mechanized proofs of type safety, termination, and security properties *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Wf.
Require Import Lia.
Import ListNotations.

(** * 1. Types *)

Inductive phr_type : Type :=
  | TInt : phr_type
  | TFloat : phr_type
  | TString : phr_type
  | TBool : phr_type
  | TIP : phr_type
  | TDateTime : phr_type
  | TList : phr_type -> phr_type
  | TRecord : list (string * phr_type) -> phr_type
  | TNull : phr_type
  | TTop : phr_type
  | TBot : phr_type.

(** A strong (nested) induction principle for [phr_type].

    The auto-generated [phr_type_ind] gives NO induction hypothesis for the
    elements of a [TRecord] field list (the recursion nests through [list] and
    [prod], which are not part of [phr_type]'s inductive block). This principle
    supplies a [Forall]-packaged IH for every field, and is reused below for
    decidable equality. The list traversal is an explicit nested [fix] so the
    guard checker accepts the recursive calls. *)
Fixpoint phr_type_ind' (P : phr_type -> Prop)
  (HInt : P TInt) (HFloat : P TFloat) (HString : P TString) (HBool : P TBool)
  (HIP : P TIP) (HDateTime : P TDateTime)
  (HList : forall t, P t -> P (TList t))
  (HRecord : forall fs, Forall (fun p => P (snd p)) fs -> P (TRecord fs))
  (HNull : P TNull) (HTop : P TTop) (HBot : P TBot)
  (t : phr_type) {struct t} : P t :=
  match t with
  | TInt => HInt | TFloat => HFloat | TString => HString | TBool => HBool
  | TIP => HIP | TDateTime => HDateTime
  | TList a => HList a (phr_type_ind' P HInt HFloat HString HBool HIP HDateTime
                          HList HRecord HNull HTop HBot a)
  | TRecord fs => HRecord fs
      ((fix flds (l : list (string * phr_type)) : Forall (fun p => P (snd p)) l :=
          match l with
          | [] => Forall_nil _
          | p :: l' => Forall_cons p
              (phr_type_ind' P HInt HFloat HString HBool HIP HDateTime
                 HList HRecord HNull HTop HBot (snd p)) (flds l')
          end) fs)
  | TNull => HNull | TTop => HTop | TBot => HBot
  end.

(** Boolean type equality.

    [decide equality] cannot dispatch the nested [TRecord (list (string *
    phr_type))] case, and a mutual [Fixpoint ... with] across [phr_type] and
    [list] is rejected by Coq's guard checker (they are not mutually inductive).
    We therefore use an explicit nested [fix] for the field list. *)
Fixpoint phr_type_eqb (t1 t2 : phr_type) {struct t1} : bool :=
  match t1, t2 with
  | TList a, TList b => phr_type_eqb a b
  | TRecord fs, TRecord gs =>
      (fix flds (xs ys : list (string * phr_type)) {struct xs} : bool :=
         match xs, ys with
         | [], [] => true
         | (f,a)::xs', (g,b)::ys' =>
             String.eqb f g && phr_type_eqb a b && flds xs' ys'
         | _, _ => false
         end) fs gs
  | TInt, TInt => true | TFloat, TFloat => true | TString, TString => true
  | TBool, TBool => true | TIP, TIP => true | TDateTime, TDateTime => true
  | TNull, TNull => true | TTop, TTop => true | TBot, TBot => true
  | _, _ => false
  end.

(** [phr_type_eqb] is reflexive. *)
Lemma phr_type_eqb_refl : forall t, phr_type_eqb t t = true.
Proof.
  induction t using phr_type_ind'; simpl; try reflexivity.
  - exact IHt.
  - induction fs as [| p fs' IHfs]; simpl.
    + reflexivity.
    + inversion H; subst. destruct p as [f a]; simpl in *.
      rewrite String.eqb_refl, H2. simpl. apply IHfs. exact H3.
Qed.

(** [phr_type_eqb] reflects equality (soundness). *)
Lemma phr_type_eqb_true : forall t1 t2, phr_type_eqb t1 t2 = true -> t1 = t2.
Proof.
  induction t1 using phr_type_ind'; intros t2 Heq; destruct t2; simpl in Heq;
    try discriminate; try reflexivity.
  - f_equal.
    match goal with IH : forall u, phr_type_eqb ?a u = true -> ?a = u |- _ =>
      apply IH; exact Heq end.
  - f_equal.
    match goal with HF : Forall _ _ |- _ => rename HF into Hall end.
    revert l Heq.
    induction Hall as [| p fs' Hhd Htail IHfs].
    + intros [| q gs'] Heq; simpl in Heq; try discriminate. reflexivity.
    + destruct p as [f a]. intros [| [g b] gs'] Heq; simpl in Heq; try discriminate.
      apply andb_prop in Heq. destruct Heq as [Hh Htl].
      apply andb_prop in Hh. destruct Hh as [Hfg Hab].
      apply String.eqb_eq in Hfg. simpl in Hhd. apply Hhd in Hab.
      apply IHfs in Htl. subst. reflexivity.
Qed.

(** Type equality is decidable (derived from the reflective Boolean equality). *)
Lemma phr_type_eq_dec : forall (t1 t2 : phr_type), {t1 = t2} + {t1 <> t2}.
Proof.
  intros t1 t2. destruct (phr_type_eqb t1 t2) eqn:E.
  - left. apply phr_type_eqb_true. exact E.
  - right. intro H. subst. rewrite phr_type_eqb_refl in E. discriminate.
Defined.

(** * 2. Values *)

Inductive phr_value : Type :=
  | VInt : Z -> phr_value
  | VFloat : Z -> phr_value  (* Placeholder for IEEE float *)
  | VString : string -> phr_value
  | VBool : bool -> phr_value
  | VIP : nat -> nat -> nat -> nat -> phr_value
  | VDateTime : Z -> phr_value
  | VList : list phr_value -> phr_value
  | VRecord : list (string * phr_value) -> phr_value
  | VNull : phr_value.

(** A strong (nested) induction principle for [phr_value] (cf. [phr_type_ind']);
    supplies a [Forall]-packaged IH for [VList] elements and [VRecord] fields. *)
Fixpoint phr_value_ind' (P : phr_value -> Prop)
  (HInt : forall z, P (VInt z)) (HFloat : forall z, P (VFloat z))
  (HString : forall s, P (VString s)) (HBool : forall b, P (VBool b))
  (HIP : forall a b c d, P (VIP a b c d)) (HDateTime : forall z, P (VDateTime z))
  (HList : forall vs, Forall P vs -> P (VList vs))
  (HRecord : forall fs, Forall (fun p => P (snd p)) fs -> P (VRecord fs))
  (HNull : P VNull)
  (v : phr_value) {struct v} : P v :=
  match v with
  | VInt z => HInt z | VFloat z => HFloat z | VString s => HString s
  | VBool b => HBool b | VIP a b c d => HIP a b c d | VDateTime z => HDateTime z
  | VList vs => HList vs
      ((fix lst (l : list phr_value) : Forall P l :=
          match l with
          | [] => Forall_nil _
          | x :: l' => Forall_cons x
              (phr_value_ind' P HInt HFloat HString HBool HIP HDateTime
                 HList HRecord HNull x) (lst l')
          end) vs)
  | VRecord fs => HRecord fs
      ((fix rcd (l : list (string * phr_value)) : Forall (fun p => P (snd p)) l :=
          match l with
          | [] => Forall_nil _
          | p :: l' => Forall_cons p
              (phr_value_ind' P HInt HFloat HString HBool HIP HDateTime
                 HList HRecord HNull (snd p)) (rcd l')
          end) fs)
  | VNull => HNull
  end.

(** Value equality is decidable (nested [fix] for the [VList]/[VRecord]
    children, since a mutual [Fixpoint ... with] across [phr_value] and [list]
    is rejected by Coq's guard checker). *)
Fixpoint value_eqb (v1 v2 : phr_value) {struct v1} : bool :=
  match v1, v2 with
  | VInt n1, VInt n2 => Z.eqb n1 n2
  | VFloat f1, VFloat f2 => Z.eqb f1 f2
  | VString s1, VString s2 => String.eqb s1 s2
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VIP a1 b1 c1 d1, VIP a2 b2 c2 d2 =>
      Nat.eqb a1 a2 && Nat.eqb b1 b2 && Nat.eqb c1 c2 && Nat.eqb d1 d2
  | VDateTime t1, VDateTime t2 => Z.eqb t1 t2
  | VList l1, VList l2 =>
      (fix lst (xs ys : list phr_value) {struct xs} : bool :=
         match xs, ys with
         | [], [] => true
         | x::xs', y::ys' => value_eqb x y && lst xs' ys'
         | _, _ => false
         end) l1 l2
  | VRecord r1, VRecord r2 =>
      (fix rcd (xs ys : list (string * phr_value)) {struct xs} : bool :=
         match xs, ys with
         | [], [] => true
         | (f,x)::xs', (g,y)::ys' => String.eqb f g && value_eqb x y && rcd xs' ys'
         | _, _ => false
         end) r1 r2
  | VNull, VNull => true
  | _, _ => false
  end.

(** value_eqb reflects equality (reflexive direction). *)
Lemma value_eqb_refl : forall v, value_eqb v v = true.
Proof.
  induction v using phr_value_ind'; simpl; try reflexivity.
  - apply Z.eqb_refl.
  - apply Z.eqb_refl.
  - apply String.eqb_refl.
  - destruct b; reflexivity.
  - rewrite !Nat.eqb_refl. reflexivity.
  - apply Z.eqb_refl.
  - match goal with HF : Forall _ _ |- _ => rename HF into Hall end.
    simpl. induction Hall as [| x vs' Hhd Htl IHvs].
    + reflexivity.
    + simpl. rewrite Hhd. simpl. exact IHvs.
  - match goal with HF : Forall _ _ |- _ => rename HF into Hall end.
    simpl. induction Hall as [| p fs' Hhd Htl IHfs].
    + reflexivity.
    + destruct p as [f x]; simpl in *. rewrite String.eqb_refl, Hhd. simpl.
      exact IHfs.
Qed.

(** * 3. Expressions *)

Inductive binop : Type :=
  | OpAdd | OpSub | OpMul | OpDiv | OpMod
  | OpAnd | OpOr
  | OpEq | OpNeq | OpLt | OpGt | OpLe | OpGe.

Inductive unop : Type :=
  | OpNot | OpNeg.

Inductive phr_expr : Type :=
  | ELit : phr_value -> phr_expr
  | EVar : string -> phr_expr
  | EBinOp : binop -> phr_expr -> phr_expr -> phr_expr
  | EUnOp : unop -> phr_expr -> phr_expr
  | EIf : phr_expr -> phr_expr -> phr_expr -> phr_expr
  | EField : phr_expr -> string -> phr_expr
  | EIn : phr_expr -> phr_expr -> phr_expr.

(** * 4. Actions *)

Inductive phr_action : Type :=
  | AAccept : option string -> phr_action
  | AReject : option string -> phr_action
  | AReport : string -> phr_action.

(** * 5. Environment (Typing Context) *)

Definition env := list (string * phr_type).

Fixpoint lookup (x : string) (e : env) : option phr_type :=
  match e with
  | [] => None
  | (y, t) :: rest => if String.eqb x y then Some t else lookup x rest
  end.

(** * 6. Value Environment *)

Definition val_env := list (string * phr_value).

Fixpoint val_lookup (x : string) (e : val_env) : option phr_value :=
  match e with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else val_lookup x rest
  end.

Fixpoint field_lookup (f : string) (fields : list (string * phr_value)) : option phr_value :=
  match fields with
  | [] => None
  | (g, v) :: rest => if String.eqb f g then Some v else field_lookup f rest
  end.

(** * 7. Is Value Predicate *)

Definition is_value (e : phr_expr) : Prop :=
  match e with
  | ELit _ => True
  | _ => False
  end.

Lemma is_value_dec : forall e, {is_value e} + {~ is_value e}.
Proof.
  destruct e; simpl; auto.
Defined.

(** * 8. Expression Size (for termination) *)

Fixpoint expr_size (e : phr_expr) : nat :=
  match e with
  | ELit _ => 1
  | EVar _ => 1
  | EBinOp _ e1 e2 => 1 + expr_size e1 + expr_size e2
  | EUnOp _ e => 1 + expr_size e
  | EIf e1 e2 e3 => 1 + expr_size e1 + expr_size e2 + expr_size e3
  | EField e _ => 1 + expr_size e
  | EIn e1 e2 => 1 + expr_size e1 + expr_size e2
  end.

Lemma expr_size_pos : forall e, expr_size e >= 1.
Proof.
  induction e; simpl; lia.
Qed.

(** * 9. Typing Relation *)

Reserved Notation "Γ '⊢' e '∈' τ" (at level 40).

Inductive has_type : env -> phr_expr -> phr_type -> Prop :=
  (* Literals *)
  | T_Int : forall Γ n,
      Γ ⊢ (ELit (VInt n)) ∈ TInt
  | T_Bool : forall Γ b,
      Γ ⊢ (ELit (VBool b)) ∈ TBool
  | T_String : forall Γ s,
      Γ ⊢ (ELit (VString s)) ∈ TString
  | T_Null : forall Γ,
      Γ ⊢ (ELit VNull) ∈ TNull
  | T_List : forall Γ vs τ,
      Forall (fun v => Γ ⊢ (ELit v) ∈ τ) vs ->
      Γ ⊢ (ELit (VList vs)) ∈ (TList τ)

  (* Variables *)
  | T_Var : forall Γ x τ,
      lookup x Γ = Some τ ->
      Γ ⊢ (EVar x) ∈ τ

  (* Arithmetic Operations *)
  | T_Add : forall Γ e1 e2,
      Γ ⊢ e1 ∈ TInt ->
      Γ ⊢ e2 ∈ TInt ->
      Γ ⊢ (EBinOp OpAdd e1 e2) ∈ TInt
  | T_Sub : forall Γ e1 e2,
      Γ ⊢ e1 ∈ TInt ->
      Γ ⊢ e2 ∈ TInt ->
      Γ ⊢ (EBinOp OpSub e1 e2) ∈ TInt
  | T_Mul : forall Γ e1 e2,
      Γ ⊢ e1 ∈ TInt ->
      Γ ⊢ e2 ∈ TInt ->
      Γ ⊢ (EBinOp OpMul e1 e2) ∈ TInt

  (* Boolean Operations *)
  | T_And : forall Γ e1 e2,
      Γ ⊢ e1 ∈ TBool ->
      Γ ⊢ e2 ∈ TBool ->
      Γ ⊢ (EBinOp OpAnd e1 e2) ∈ TBool
  | T_Or : forall Γ e1 e2,
      Γ ⊢ e1 ∈ TBool ->
      Γ ⊢ e2 ∈ TBool ->
      Γ ⊢ (EBinOp OpOr e1 e2) ∈ TBool

  (* Comparison Operations *)
  | T_Eq : forall Γ e1 e2 τ,
      Γ ⊢ e1 ∈ τ ->
      Γ ⊢ e2 ∈ τ ->
      Γ ⊢ (EBinOp OpEq e1 e2) ∈ TBool
  | T_Lt : forall Γ e1 e2,
      Γ ⊢ e1 ∈ TInt ->
      Γ ⊢ e2 ∈ TInt ->
      Γ ⊢ (EBinOp OpLt e1 e2) ∈ TBool

  (* Unary Operations *)
  | T_Not : forall Γ e,
      Γ ⊢ e ∈ TBool ->
      Γ ⊢ (EUnOp OpNot e) ∈ TBool
  | T_Neg : forall Γ e,
      Γ ⊢ e ∈ TInt ->
      Γ ⊢ (EUnOp OpNeg e) ∈ TInt

  (* Conditionals *)
  | T_If : forall Γ e1 e2 e3 τ,
      Γ ⊢ e1 ∈ TBool ->
      Γ ⊢ e2 ∈ τ ->
      Γ ⊢ e3 ∈ τ ->
      Γ ⊢ (EIf e1 e2 e3) ∈ τ

  (* Membership *)
  | T_In : forall Γ e1 e2 τ,
      Γ ⊢ e1 ∈ τ ->
      Γ ⊢ e2 ∈ (TList τ) ->
      Γ ⊢ (EIn e1 e2) ∈ TBool

  (* Field Access *)
  | T_Field : forall Γ e f fields τ,
      Γ ⊢ e ∈ (TRecord fields) ->
      In (f, τ) fields ->
      Γ ⊢ (EField e f) ∈ τ

where "Γ '⊢' e '∈' τ" := (has_type Γ e τ).

(** * 10. Value Typing *)

Inductive value_has_type : phr_value -> phr_type -> Prop :=
  | VT_Int : forall n, value_has_type (VInt n) TInt
  | VT_Bool : forall b, value_has_type (VBool b) TBool
  | VT_String : forall s, value_has_type (VString s) TString
  | VT_Null : value_has_type VNull TNull
  | VT_List : forall vs τ,
      Forall (fun v => value_has_type v τ) vs ->
      value_has_type (VList vs) (TList τ)
  | VT_Record : forall fields ftypes,
      (forall f τ, In (f, τ) ftypes ->
        exists v, field_lookup f fields = Some v /\ value_has_type v τ) ->
      value_has_type (VRecord fields) (TRecord ftypes).

(** * 11. Evaluation Relation *)

Reserved Notation "ρ '⊢' e '⇓' v" (at level 40).

Definition value_inb (v : phr_value) (vs : list phr_value) : bool :=
  existsb (value_eqb v) vs.

Inductive eval : val_env -> phr_expr -> phr_value -> Prop :=
  (* Literals *)
  | E_Lit : forall ρ v,
      ρ ⊢ (ELit v) ⇓ v

  (* Variables *)
  | E_Var : forall ρ x v,
      val_lookup x ρ = Some v ->
      ρ ⊢ (EVar x) ⇓ v

  (* Integer Arithmetic *)
  | E_Add : forall ρ e1 e2 n1 n2,
      ρ ⊢ e1 ⇓ (VInt n1) ->
      ρ ⊢ e2 ⇓ (VInt n2) ->
      ρ ⊢ (EBinOp OpAdd e1 e2) ⇓ (VInt (n1 + n2))
  | E_Sub : forall ρ e1 e2 n1 n2,
      ρ ⊢ e1 ⇓ (VInt n1) ->
      ρ ⊢ e2 ⇓ (VInt n2) ->
      ρ ⊢ (EBinOp OpSub e1 e2) ⇓ (VInt (n1 - n2))
  | E_Mul : forall ρ e1 e2 n1 n2,
      ρ ⊢ e1 ⇓ (VInt n1) ->
      ρ ⊢ e2 ⇓ (VInt n2) ->
      ρ ⊢ (EBinOp OpMul e1 e2) ⇓ (VInt (n1 * n2))

  (* Boolean And (short-circuit) *)
  | E_And_True : forall ρ e1 e2 b,
      ρ ⊢ e1 ⇓ (VBool true) ->
      ρ ⊢ e2 ⇓ (VBool b) ->
      ρ ⊢ (EBinOp OpAnd e1 e2) ⇓ (VBool b)
  | E_And_False : forall ρ e1 e2,
      ρ ⊢ e1 ⇓ (VBool false) ->
      ρ ⊢ (EBinOp OpAnd e1 e2) ⇓ (VBool false)

  (* Boolean Or (short-circuit) *)
  | E_Or_True : forall ρ e1 e2,
      ρ ⊢ e1 ⇓ (VBool true) ->
      ρ ⊢ (EBinOp OpOr e1 e2) ⇓ (VBool true)
  | E_Or_False : forall ρ e1 e2 b,
      ρ ⊢ e1 ⇓ (VBool false) ->
      ρ ⊢ e2 ⇓ (VBool b) ->
      ρ ⊢ (EBinOp OpOr e1 e2) ⇓ (VBool b)

  (* Equality *)
  | E_Eq : forall ρ e1 e2 v1 v2,
      ρ ⊢ e1 ⇓ v1 ->
      ρ ⊢ e2 ⇓ v2 ->
      ρ ⊢ (EBinOp OpEq e1 e2) ⇓ (VBool (value_eqb v1 v2))

  (* Less Than *)
  | E_Lt : forall ρ e1 e2 n1 n2,
      ρ ⊢ e1 ⇓ (VInt n1) ->
      ρ ⊢ e2 ⇓ (VInt n2) ->
      ρ ⊢ (EBinOp OpLt e1 e2) ⇓ (VBool (Z.ltb n1 n2))

  (* Not *)
  | E_Not : forall ρ e b,
      ρ ⊢ e ⇓ (VBool b) ->
      ρ ⊢ (EUnOp OpNot e) ⇓ (VBool (negb b))

  (* Negation *)
  | E_Neg : forall ρ e n,
      ρ ⊢ e ⇓ (VInt n) ->
      ρ ⊢ (EUnOp OpNeg e) ⇓ (VInt (- n))

  (* Conditional - True *)
  | E_If_True : forall ρ e1 e2 e3 v,
      ρ ⊢ e1 ⇓ (VBool true) ->
      ρ ⊢ e2 ⇓ v ->
      ρ ⊢ (EIf e1 e2 e3) ⇓ v

  (* Conditional - False *)
  | E_If_False : forall ρ e1 e2 e3 v,
      ρ ⊢ e1 ⇓ (VBool false) ->
      ρ ⊢ e3 ⇓ v ->
      ρ ⊢ (EIf e1 e2 e3) ⇓ v

  (* List Membership *)
  | E_In : forall ρ e1 e2 v vs,
      ρ ⊢ e1 ⇓ v ->
      ρ ⊢ e2 ⇓ (VList vs) ->
      ρ ⊢ (EIn e1 e2) ⇓ (VBool (value_inb v vs))

  (* Field Access *)
  | E_Field : forall ρ e f fields v,
      ρ ⊢ e ⇓ (VRecord fields) ->
      field_lookup f fields = Some v ->
      ρ ⊢ (EField e f) ⇓ v

where "ρ '⊢' e '⇓' v" := (eval ρ e v).

(** * 12. Canonical Forms Lemma *)

Lemma canonical_forms_int : forall v,
  value_has_type v TInt ->
  exists n, v = VInt n.
Proof.
  intros v Htype.
  inversion Htype; subst.
  exists n. reflexivity.
Qed.

Lemma canonical_forms_bool : forall v,
  value_has_type v TBool ->
  exists b, v = VBool b.
Proof.
  intros v Htype.
  inversion Htype; subst.
  exists b. reflexivity.
Qed.

Lemma canonical_forms_list : forall v τ,
  value_has_type v (TList τ) ->
  exists vs, v = VList vs /\ Forall (fun w => value_has_type w τ) vs.
Proof.
  intros v τ Htype.
  inversion Htype; subst.
  exists vs. split; auto.
Qed.

(** * 13. Type Safety: Preservation *)

(** List helper: zip per-element type-preservation with per-element typing. *)
Lemma literal_preservation_list : forall Γ vs τ,
  Forall (fun w => forall Γ' τ', Γ' ⊢ (ELit w) ∈ τ' -> value_has_type w τ') vs ->
  Forall (fun w => Γ ⊢ (ELit w) ∈ τ) vs ->
  Forall (fun w => value_has_type w τ) vs.
Proof.
  intros Γ vs. induction vs as [| w ws IHvs]; intros τ Hih Het.
  - constructor.
  - pose proof (Forall_inv Hih) as Hw.
    pose proof (Forall_inv_tail Hih) as Hihs.
    pose proof (Forall_inv Het) as Hwt.
    pose proof (Forall_inv_tail Het) as Hets.
    constructor.
    + eapply Hw. exact Hwt.
    + apply IHvs; assumption.
Qed.

(** A well-typed literal value has the corresponding value type. Proved by the
    strong value induction so the [VList] case can convert element typings. *)
Lemma literal_preservation : forall v Γ τ,
  Γ ⊢ (ELit v) ∈ τ -> value_has_type v τ.
Proof.
  intros v. induction v using phr_value_ind'; intros Γ τ Ht; inversion Ht; subst.
  - constructor.            (* VInt  -> TInt  *)
  - constructor.            (* VString -> TString *)
  - constructor.            (* VBool -> TBool *)
  - constructor.            (* VList vs -> TList τ0 *)
    apply (literal_preservation_list Γ); assumption.
  - constructor.            (* VNull -> TNull *)
Qed.

(** Preservation (type safety): a well-typed closed expression evaluates to a
    value of its type. By induction on the evaluation derivation, which keeps
    the typing context concrete ([]) so the [EVar] case is genuinely impossible. *)
Theorem preservation : forall ρ e τ v,
  [] ⊢ e ∈ τ ->
  ρ ⊢ e ⇓ v ->
  value_has_type v τ.
Proof.
  intros ρ e τ v Htype Heval.
  generalize dependent τ.
  induction Heval; intros τ Htype;
    try (inversion Htype; subst; now constructor).
  - (* E_Lit *) eapply literal_preservation. exact Htype.
  - (* E_Var: a variable is untypable in the empty context *)
    inversion Htype; subst.
    match goal with H : lookup _ [] = Some _ |- _ => simpl in H; discriminate H end.
  - (* E_If_True *) inversion Htype; subst. apply IHHeval2. assumption.
  - (* E_If_False *) inversion Htype; subst. apply IHHeval2. assumption.
  - (* E_Field: the looked-up field value has the field's type *)
    inversion Htype; subst.
    match goal with Hrec : has_type [] ?ee (TRecord ?ff) |- _ =>
      specialize (IHHeval (TRecord ff) Hrec) end.
    inversion IHHeval; subst.
    match goal with
      Hbody : forall f0 t, In (f0, t) ?ff -> _,
      Hin : In (?f1, τ) ?ff |- _ =>
        destruct (Hbody f1 τ Hin) as [w [Hlk Hwt]]
    end.
    assert (v = w) by congruence. subst. exact Hwt.
Qed.

(** * 14. Evaluation is Deterministic *)

Theorem eval_deterministic : forall ρ e v1 v2,
  ρ ⊢ e ⇓ v1 ->
  ρ ⊢ e ⇓ v2 ->
  v1 = v2.
Proof.
  intros ρ e v1 v2 H1.
  generalize dependent v2.
  (* For each evaluation rule of the first derivation, invert the second; then
     resolve every shared subexpression by its induction hypothesis (which says
     the subexpression evaluates to a unique value) and close by congruence.
     Short-circuit boolean cases close because the IH forces a contradictory
     guard value; the field case closes via field_lookup on equal records. *)
  induction H1; intros vR H2; inversion H2; subst;
    repeat match goal with
    | [ IH : forall v, _ ⊢ ?e ⇓ v -> _ = v, Hv : _ ⊢ ?e ⇓ _ |- _ ] =>
        apply IH in Hv
    end;
    try reflexivity; try congruence.
Qed.

(** * 15. Termination *)

(** Expression evaluation terminates because:
    1. All expressions have finite size
    2. No recursion in the language
    3. Each evaluation rule processes subexpressions *)

(** Define the termination measure: expression size *)
Lemma termination_measure : forall e,
  exists n, expr_size e = n /\ n >= 1.
Proof.
  intros e.
  exists (expr_size e).
  split.
  - reflexivity.
  - apply expr_size_pos.
Qed.

(** Free variables of an expression. *)
Fixpoint free_vars (e : phr_expr) : list string :=
  match e with
  | ELit _ => []
  | EVar x => [x]
  | EBinOp _ e1 e2 => free_vars e1 ++ free_vars e2
  | EUnOp _ e => free_vars e
  | EIf e1 e2 e3 => free_vars e1 ++ free_vars e2 ++ free_vars e3
  | EField e _ => free_vars e
  | EIn e1 e2 => free_vars e1 ++ free_vars e2
  end.

(** Totality / progress-to-a-value: a well-typed closed expression always
    evaluates to a value (the language has no loops or recursion).

    NOTE: the ORIGINAL statement required only that the value environment cover
    [free_vars e], which is FALSE — e.g. [EBinOp OpAdd (ELit (VBool true))
    (ELit (VInt 1))] is closed but has no applicable evaluation rule. The
    correct hypothesis is WELL-TYPEDNESS; and since [[] ⊢ e ∈ τ] already forces
    [e] to be closed (there is no binding form, so [EVar] is untypable here),
    the value-environment hypothesis is redundant and dropped. The proof is an
    induction on [e] that uses [preservation] + the canonical value shapes to
    pin each operand. [ρ] is arbitrary precisely because [e] is closed. *)
Theorem totality : forall e τ ρ,
  [] ⊢ e ∈ τ -> exists v, ρ ⊢ e ⇓ v.
Proof.
  intros e; induction e as
    [ p | s | b e1 IHe1 e2 IHe2 | u e IHe
    | e1 IHe1 e2 IHe2 e3 IHe3 | e IHe f | e1 IHe1 e2 IHe2 ];
    intros τ ρ Ht.
  - (* ELit *) exists p. constructor.
  - (* EVar: untypable in the empty context *)
    inversion Ht; subst.
    match goal with H : lookup _ [] = Some _ |- _ => simpl in H; discriminate H end.
  - (* EBinOp: evaluate the left operand once, up front *)
    inversion Ht; subst;
    match goal with Ha : has_type [] e1 _ |- _ =>
      destruct (IHe1 _ ρ Ha) as [v1 Hv1];
      pose proof (preservation _ _ _ _ Ha Hv1) as T1
    end.
    + (* Add *) match goal with Hb : has_type [] e2 _ |- _ =>
        destruct (IHe2 _ ρ Hb) as [v2 Hv2]; pose proof (preservation _ _ _ _ Hb Hv2) as T2 end;
        inversion T1; subst; inversion T2; subst; eexists; apply E_Add; eassumption.
    + (* Sub *) match goal with Hb : has_type [] e2 _ |- _ =>
        destruct (IHe2 _ ρ Hb) as [v2 Hv2]; pose proof (preservation _ _ _ _ Hb Hv2) as T2 end;
        inversion T1; subst; inversion T2; subst; eexists; apply E_Sub; eassumption.
    + (* Mul *) match goal with Hb : has_type [] e2 _ |- _ =>
        destruct (IHe2 _ ρ Hb) as [v2 Hv2]; pose proof (preservation _ _ _ _ Hb Hv2) as T2 end;
        inversion T1; subst; inversion T2; subst; eexists; apply E_Mul; eassumption.
    + (* And: short-circuit on the left guard *)
      inversion T1; subst;
      match goal with Hg : _ ⊢ e1 ⇓ VBool ?bb |- _ => destruct bb end.
      * match goal with Hb : has_type [] e2 _ |- _ =>
          destruct (IHe2 _ ρ Hb) as [v2 Hv2]; pose proof (preservation _ _ _ _ Hb Hv2) as T2 end;
          inversion T2; subst; eexists; apply E_And_True; eassumption.
      * eexists; apply E_And_False; eassumption.
    + (* Or: short-circuit on the left guard *)
      inversion T1; subst;
      match goal with Hg : _ ⊢ e1 ⇓ VBool ?bb |- _ => destruct bb end.
      * eexists; apply E_Or_True; eassumption.
      * match goal with Hb : has_type [] e2 _ |- _ =>
          destruct (IHe2 _ ρ Hb) as [v2 Hv2]; pose proof (preservation _ _ _ _ Hb Hv2) as T2 end;
          inversion T2; subst; eexists; apply E_Or_False; eassumption.
    + (* Eq: no value-shape constraint *)
      match goal with Hb : has_type [] e2 _ |- _ =>
        destruct (IHe2 _ ρ Hb) as [v2 Hv2] end;
        eexists; apply E_Eq; eassumption.
    + (* Lt *) match goal with Hb : has_type [] e2 _ |- _ =>
        destruct (IHe2 _ ρ Hb) as [v2 Hv2]; pose proof (preservation _ _ _ _ Hb Hv2) as T2 end;
        inversion T1; subst; inversion T2; subst; eexists; apply E_Lt; eassumption.
  - (* EUnOp *)
    inversion Ht; subst;
    match goal with Ha : has_type [] e _ |- _ =>
      destruct (IHe _ ρ Ha) as [v Hv]; pose proof (preservation _ _ _ _ Ha Hv) as T end;
      inversion T; subst.
    + eexists; apply E_Not; eassumption.
    + eexists; apply E_Neg; eassumption.
  - (* EIf: branch on the guard value *)
    inversion Ht; subst.
    match goal with Hc : has_type [] e1 _ |- _ =>
      destruct (IHe1 _ ρ Hc) as [v1 Hv1]; pose proof (preservation _ _ _ _ Hc Hv1) as T1 end.
    inversion T1; subst.
    match goal with Hg : _ ⊢ e1 ⇓ VBool ?bb |- _ => destruct bb end.
    + match goal with Ht2 : has_type [] e2 _ |- _ =>
        destruct (IHe2 _ ρ Ht2) as [v2 Hv2] end; exists v2; apply E_If_True; assumption.
    + match goal with Ht3 : has_type [] e3 _ |- _ =>
        destruct (IHe3 _ ρ Ht3) as [v3 Hv3] end; exists v3; apply E_If_False; assumption.
  - (* EField: the field exists in the (well-typed) record value *)
    inversion Ht; subst.
    match goal with Hr : has_type [] e (TRecord ?ff), Hin : In (f, τ) ?ff |- _ =>
      destruct (IHe _ ρ Hr) as [v Hv]; pose proof (preservation _ _ _ _ Hr Hv) as T;
      inversion T; subst;
      match goal with Hbody : forall a t, In (a, t) ff -> _ |- _ =>
        destruct (Hbody f τ Hin) as [w [Hlk Hwt]]
      end
    end.
    exists w. eapply E_Field; eassumption.
  - (* EIn: the right operand is a list value *)
    inversion Ht; subst.
    match goal with
      Ha : has_type [] e1 _, Hb : has_type [] e2 (TList _) |- _ =>
        destruct (IHe1 _ ρ Ha) as [v1 Hv1];
        destruct (IHe2 _ ρ Hb) as [v2 Hv2];
        pose proof (preservation _ _ _ _ Hb Hv2) as T2
    end.
    inversion T2; subst. eexists. apply E_In; eassumption.
Qed.

(** * 16. Type Safety Corollary *)

Corollary type_safety : forall e τ ρ v,
  [] ⊢ e ∈ τ ->
  ρ ⊢ e ⇓ v ->
  value_has_type v τ.
Proof.
  intros e τ ρ v Htype Heval. exact (preservation ρ e τ v Htype Heval).
Qed.

(** * 17. Sandbox Isolation *)

(** The grammar does not include system calls, file operations, or network
    operations. This is enforced BY CONSTRUCTION: [phr_expr] is first-order and
    has no application/call/IO constructor.

    NOTE (honesty): the previous [no_system_calls] statement was unsound — it
    asserted that no expression equals [ELit (VString "system")], which is false
    ([ELit (VString "system")] is a perfectly good inert string literal). The
    sandbox guarantee is not "the string 'system' cannot appear" but "there is
    no expression form that INVOKES anything". We capture that honestly below:
    every expression is one of the seven inert forms, none of which is a call. *)

Theorem sandbox_no_call_form : forall e : phr_expr,
  (exists v, e = ELit v) \/ (exists x, e = EVar x) \/
  (exists o a b, e = EBinOp o a b) \/ (exists o a, e = EUnOp o a) \/
  (exists a b c, e = EIf a b c) \/ (exists a f, e = EField a f) \/
  (exists a b, e = EIn a b).
Proof.
  destruct e.
  - left; eauto.
  - right; left; eauto.
  - right; right; left; eauto.
  - right; right; right; left; eauto.
  - right; right; right; right; left; eauto.
  - right; right; right; right; right; left; eauto.
  - right; right; right; right; right; right; eauto.
Qed.

(** * 18. Subtyping *)

Reserved Notation "τ1 '<:' τ2" (at level 40).

Inductive subtype : phr_type -> phr_type -> Prop :=
  | Sub_Refl : forall τ, τ <: τ
  | Sub_Bot : forall τ, TBot <: τ
  | Sub_Top : forall τ, τ <: TTop
  | Sub_List : forall τ1 τ2,
      τ1 <: τ2 ->
      (TList τ1) <: (TList τ2)
where "τ1 '<:' τ2" := (subtype τ1 τ2).

(** Subtyping is transitive *)
Theorem subtype_trans : forall τ1 τ2 τ3,
  τ1 <: τ2 -> τ2 <: τ3 -> τ1 <: τ3.
Proof.
  intros τ1 τ2 τ3 H12. generalize dependent τ3.
  induction H12; intros τ3 H23.
  - assumption.
  - apply Sub_Bot.
  - inversion H23; subst; apply Sub_Top.
  - inversion H23; subst; eauto using Sub_List, Sub_Top.
Qed.

(** * 19. Summary *)

(**
   This formalization proves:

   1. TYPE SAFETY (Preservation):
      If e : τ and e ⇓ v, then v : τ

   2. DETERMINISM:
      If e ⇓ v1 and e ⇓ v2, then v1 = v2

   3. TERMINATION:
      All expressions have finite size, no recursion

   4. SANDBOX ISOLATION:
      No system calls expressible in the grammar

   5. SUBTYPING:
      Reflexive and transitive subtype relation

   For consensus properties, see TLA+ specification.
*)

(** End of Phronesis formalization *)
