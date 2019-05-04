Require Coq.Arith.Plus.
Require Import Eqdep.
(** Dependent Inductive Types **)
(*******************************)

Section vectors.
  Variable T : Type.

  Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, T -> vector n -> vector (S n).

Print vector.
(*
  Arguments Vcons {_} _ _.
  Arguments Vnil.
*)

  Fixpoint vappend {n m : nat} (v1 : vector n) (v2 : vector m) {struct v1}
  : vector (n + m) := 
    match v1 in vector l' return vector (l' + m) with
    | Vnil => v2
    | Vcons x xs => Vcons x (vappend xs v2)
    end.



  Definition Vcast (n m : nat) (pf : n = m)
  : vector n -> vector m :=
    match pf in _ = k 
             return (vector n -> vector k)
    with
    | eq_refl => fun x => x
    end.



  (* We can use dependent pattern matching on equality
   * proofs to state the associativity of [vappend].
   *)

(*
Theorem vappend_assoc
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc = vappend va (vappend vb vc).

*)        


  Check Plus.plus_assoc.


(*

Plus.plus_assoc
     : forall n m p : nat, n + (m + p) = (n + m) + p

*)

Check UIP_refl.

Check UIP_refl nat.

  Theorem vappend_assoc_UIP
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc (*vector ((a+b)+c) *)
      = match Plus.plus_assoc a b c in _ = X return vector X with
        | eq_refl => vappend va (vappend vb vc) 
                     (*vector (a + (b+c))*)
        end.
  Proof.
    induction va.
    - simpl. 
      intros.
      (*generalize (vappend vb vc).*) 
      generalize (Plus.plus_assoc 0 b c).
      intro.
      simpl in e.
      rewrite (UIP_refl nat (b+c) e).
      trivial. 
    - simpl. intros. rewrite IHva.
      (*generalize (vappend va (vappend vb vc)).
      intro.*)
      generalize (Plus.plus_assoc n b c).
      generalize (Plus.plus_assoc (S n) b c).
      clear IHva.
      intros.
      simpl in e.
      revert e0 e.
      generalize (n + b + c).
      intros. 
      destruct e0.
      rewrite (UIP_refl nat (S (n + (b + c))) e).
      trivial.
Qed.

(*
Recall:

UIP_refl_nat is provable in Coq and there is no need to use axiom UIP_refl 

*)

  (* Everything will work out if we have a transparent definition of
   * plus_assoc.
   *)
  Lemma plus_assoc_trans : forall n m p : nat, n + (m + p) = n + m + p.
  Proof.
    induction n.
    { reflexivity. }
    { simpl. intros. f_equal. apply IHn. }
  Defined.

Print plus_assoc_trans.

  Theorem vappend_assoc
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc
      = match plus_assoc_trans a b c in _ = X return vector X with
        | eq_refl => vappend va (vappend vb vc)
        end.
  Proof. 
    induction va.
    - simpl. reflexivity.
    - simpl. intros. rewrite IHva.
      clear IHva.
      destruct (plus_assoc_trans n b c).
      simpl.
      reflexivity.
 Qed.

(*
How destruct works ? Informally: replaces y with x in the goal....
*) 
 
Lemma des: forall x y z (P:nat-> nat ->Type), 
           x=y -> (P (0+y) y)= (P z z) -> (P x x)=(P z z).
intros x y z P H.
destruct H.
trivial.
Qed.

Print des.

  




