Set Implicit Arguments.

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

Inductive type : Set := TNat | TBool.

Locate "+".

Print sumbool.

(*
Inductive sumbool (A B : Prop) : Set :=
    left : A -> {A} + {B} | right : B -> {A} + {B}
*)

Definition eq_type_dec: forall (t1 t2:type), {t1=t2}+{t1<>t2}.
decide equality.
Qed.

Print eq_type_dec.


Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.


Lemma hasType_det : forall e t1, hasType e t1 ->
 forall t2, hasType e t2 -> t1 = t2.
  induction e.
  inversion 1.
  inversion 1;auto.
  inversion 1.
  inversion 1;auto.
  inversion 1.
  inversion 1;auto.
  inversion 1.
  inversion 1;auto.
Restart.
  induction 1.
  inversion 1; auto. 
  inversion 1;auto. 
  inversion 1;auto. 
  inversion 1;auto.
Restart.
  induction 1;  inversion 1; auto.
Qed.

