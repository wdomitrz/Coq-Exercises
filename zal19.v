Set Implicit Arguments.
Require Import  List.
Require Import Eqdep.
Require Import Eqdep_dec.
Require Import Omega.


(* Coq assignment - ZPF 2019 - due to 14.05.2019

Fill the definitions and prove the lemmas given below (replace 
Admitted with Qed).

It is not allowed to: 
1. change/erase given definitions and lemma statements,
   section header/footer, variable declaration, etc.,
2. introduce your own axioms, parameters, variables, hypotheses etc.,   
3. import other modules,
4. define Ltac tactics.

It is allowed to:
1. introduce your own definitions and auxiliary lemmas,
2. change the order of the lemmas to prove,
3. add comments. 

Submit your solution via email before 23:59 on 14.05.2019. 
You should submit one file named zal.v containing your proofs.

The author of the assignment and the grader is Daria Walukiewicz-Chrząszcz.

*)

Section filterL.
(*------------------------------------------------------------------
Nondependent case : filter on lists
--------------------------------------------------------------------
*)
Set Printing All.
Print list.

Variable A : Type.
Variable P : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.

Fixpoint filterL (l:list A) : list A :=
match l with
| nil => nil
| cons a l' => if P_dec a then cons a (filterL l') else filterL l'
end.

Fixpoint countPL (l : list A) := 
match l with 
| nil => O
| cons x l' => if P_dec x then S (countPL l') else countPL l'
end.


(* Prove lemmas cPL1 and cPL2 *)

Print Forall.

Lemma cPL1: forall (l:list A), countPL l = 0 -> 
           Forall (fun x => ~P x) l.
Proof.
  intros.
  induction l.
  * apply Forall_nil.
  * simpl countPL in H.
    case (P_dec a) in H.
    - congruence.
    - apply Forall_cons.
      + assumption.
      + apply (IHl H).
Qed.

Lemma cPL2_helper: forall (l:list A), countPL l <= length l.
Proof.
  induction l.
  * simpl.
    trivial.
  * simpl.
    case (P_dec a).
    + intro.
      apply le_n_S.
      assumption.
    + intro.
      apply le_S.
      assumption.
Qed.

Lemma cPL2_helper2: forall (l:list A), countPL l = S (length l) -> False.
Proof.
  intros.
  induction l.
  * simpl countPL in H.

Admitted.

Lemma cPL2: forall (l:list A), countPL l = length l -> Forall P l.
Proof.
  intros.
  induction l.
  * apply Forall_nil.
  * simpl countPL in H.
    simpl length in H.
    destruct (P_dec a).
    + apply Forall_cons; try apply IHl.
      - assumption.
      - inversion H.
        reflexivity.
    + exfalso.
      apply (cPL2_helper2 l).
      assumption.
Qed.

Print cPL2.


(* in case of troubles: think about the lengths of the lists *)

End filterL.


Section filterV.
(*------------------------------------------------------------------
Dependent case: filter on vectors
--------------------------------------------------------------------
*)


Variable A : Type.
Variable P : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.


Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, A -> vector n -> vector (S n).

  Arguments Vcons {_} _ _.

(*
Write the definition of countPV on vectors; it should correspond to countPL 
Use keyword Fixpoint
*)

Fixpoint countPV {n : nat} (v : vector n) := 
match v with 
| Vnil => O
| Vcons a v' => if P_dec a then S (countPV v') else countPV v'
end.

(*
Write the definition of filterV on vectors; it should correspond to filterL.
Use keyword Fixpoint
*)

Fixpoint filterV {n : nat} (v : vector n) : vector (countPV v) :=
match v with
| Vnil => Vnil
| Vcons a v' =>
    (match (P_dec a) as z return (vector
      (match z with
      | right _ => (countPV v')
      | left _ => (S (countPV v'))
      end))
    with
    | right ph => (filterV v')
    | left ph => Vcons a (filterV v')
    end)
end.

(*
ForallV is Forall on vectors
*)

Print Forall.

Inductive ForallV (P:A-> Prop): forall {n:nat}, vector n -> Prop :=
    Forall_Vnil : ForallV P Vnil
  | Forall_Vcons : forall (x : A) (n:nat) (v : vector n),
                  P x -> ForallV P v -> ForallV P (Vcons x v).

(* 
Write the definition of the last element of a nonempty vector. 
Do it twice:
- using tactics in proof-mode
- using Fixpoint and match

Fill:
*)

Definition elemType n : Type := match n with
  | 0 => vector 0
  | S n' => A
end.

Definition lastType n : Type := elemType n.

Lemma lastLemma: forall {n: nat} (v : vector n), lastType n.
Proof.
  intros.
  induction n.
  * simpl.
    assumption.
  * simpl.
    destruct n.
    + inversion v.
      assumption.
    + inversion v.
      apply IHn.
      assumption.
Defined.



Definition lastOfNonemptyByProof {n:nat} (v:vector (S n)): A := lastLemma v.

Lemma head: forall {n: nat} (v : vector (S n)), A.
Proof.
  intros.
  inversion v.
  assumption.
Qed.

Lemma splitVectorLemma {n: nat} (v: vector (S n)): (A * vector n).
Proof.
  inversion v.
  info_auto.
Qed.

Print splitVectorLemma.

Fixpoint splitVector {n: nat} (v: vector (S n)): (A * vector n) :=
  (match v in (vector n') return (n' = S n -> A * vector n) with
  | Vnil =>
      fun H =>
      (fun H0 =>
       let H1 :=
         eq_ind 0
           (fun e : nat => match e with
                           | 0 => True
                           | S _ => False
                           end) I (S n) H0
         :
         False in
       False_rect (A * vector n) H1) H
  | @Vcons n' a v' =>
      fun H : S n' = S n =>
      (fun H0 : S n' = S n =>
       let H1 :=
         f_equal (fun e : nat => match e with
                                 | 0 => n'
                                 | S n'' => n''
                                 end) H0
         :
         n' = n in
       (fun H2 : n' = n =>
        let H3 := H2 : n' = n in
        eq_rect_r (fun n'' : nat => A -> vector n'' -> A * vector n)
          (fun (X1 : A) (X2 : vector n) => (X1, X2)) H3) H1) H a v'
  end) eq_refl.

Fixpoint lastFixpoint {n: nat}: vector n ->  lastType n:=
match n as x return (vector x -> lastType x) with
| O => fun t => t
| S m => fun t (* tuple S m *) =>
   (match m as n1 return ((vector n1 -> lastType n1) -> vector (S n1) -> A)
   with
   | 0 => fun _ H => let (t, _) := splitVector H in t
   | S n1 => fun IHn0 X => IHn0 (let (_,t0) := splitVector X in let (t1,t2) := splitVector t0 in Vcons t1 t2)
   end) (@lastFixpoint m) t
end.


Definition lastOfNonemptyByHand {n:nat} (v:vector (S n)) : A := lastFixpoint v.


Variable e1 e2 e3:A.

(*
and test it:
*)
Eval compute in (lastOfNonemptyByProof (Vcons e1 (Vcons e2 (Vcons e3 Vnil)))). 
Eval compute in (lastOfNonemptyByHand (Vcons e1 (Vcons e2 (Vcons e3 Vnil)))). 

(* 
Prove lemmas cPV1 and cPV2
*)

(*
Inductive ForallV (P:A-> Prop): forall {n:nat}, vector n -> Prop :=
    Forall_Vnil : ForallV P Vnil
  | Forall_Vcons : forall (x : A) (n:nat) (v : vector n),
                  P x -> ForallV P v -> ForallV P (Vcons x v).
                  *)

Lemma cPV1: forall (n:nat)(v:vector n), countPV v = 0 -> 
           ForallV (fun x => ~P x) v.
Proof.
  intros.
  induction v.
  *
Admitted.


Lemma cPV2: forall (n:nat) (v:vector n), countPV v = n -> ForallV P v.
Proof.
Admitted.

(* Recall that UIP_refl nat is provable in Coq *)

Check (UIP_refl nat).


(*
Prove the following inversion lemma 
*)


Lemma cPVInversion: forall (n:nat) (a:A) (v:vector n), 
      S n = countPV (Vcons a v) -> (P a /\ n = countPV v).
Proof.
  intros.
  pose proof (countPV (Vcons a v) = S n).
  pose proof (cPV2 (Vcons a v)).
  rewrite <- H in H0.
  split.
  
Qed.

(*
Prove cPVfilterVIdentity
*)


Lemma cPVfilterVIdentity: forall (n:nat) (v:vector n) (d: n = countPV v),
filterV v = match d in _= n' return vector n' with
                            | eq_refl => v
                            end.
Proof.
  intros.
  induction v; try simpl.
  * simpl.
    rewrite (UIP_refl nat 0 d).
    reflexivity.
  *
Admitted.


(* 
cPVtc is a type-cast needed to formulate the lemma given below
*)

Lemma cPVtc : forall {n:nat} (v:vector n),  countPV v = countPV (filterV v).
Proof.
  intros.
  induction v.
  * trivial.
  * simpl.
    case (P_dec a); try intros.
    + simpl countPV.
      case (P_dec a); try intros.
      - rewrite <- IHv.
        reflexivity.
      - contradiction.
    + assumption.
Qed.

(* 
Use the lemmas proved above to show that filterV is idempotent
*)
 

Lemma filterV_idem: forall {n:nat} (v:vector n),
      filterV (filterV v) = match cPVtc v in _= n' return vector n' with
                            | eq_refl => filterV v
                            end.
Proof.
  intros.
  apply cPVfilterVIdentity.
Qed.

End filterV.
