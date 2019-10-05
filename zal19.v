Set Implicit Arguments.
Require Import  List.
Require Import Eqdep.
Require Import Eqdep_dec.
Require Import Omega.


(* Coq assignment - ZPF 2019 - due to 07.05.2019

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

Submit your solution via email before 23:59 on 07.05.2019. 
You should submit one file named zal.v containing your proofs.

The author of the assignment and the grader is Daria Walukiewicz-Chrząszcz.

*)

Section filterL.
(*------------------------------------------------------------------
Nondependent case : filter on lists
--------------------------------------------------------------------
*)

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
Admitted.


Lemma cPL2: forall (l:list A), countPL l = length l -> Forall P l.
Proof.
Admitted.


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

(*
Write the definition of filterV on vectors; it should correspond to filterL.
Use keyword Fixpoint
*)

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

Definition lastOfNonemptyByProof {n:nat} (v:vector (S n)): A := 
Definition lastOfNonemptyByHand {n:nat} (v:vector (S n)) : A := 
*)

Variable e1 e2 e3:A.

(*
and test it:

Eval compute in (lastOfNonemptyByProof (Vcons e1 (Vcons e2 (Vcons e3 Vnil)))). 
Eval compute in (lastOfNonemptyByHand (Vcons e1 (Vcons e2 (Vcons e3 Vnil)))). 
*)


(* 
Prove lemmas cPV1 and cPV2
*)

Lemma cPV1: forall (n:nat)(v:vector n), countPV v = 0 -> 
           ForallV (fun x => ~P x) v.
Proof.
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
Admitted.

(*
Prove cPVfilterVIdentity
*)


Lemma cPVfilterVIdentity: forall (n:nat) (v:vector n) (d: n = countPV v),
filterV v = match d in _= m return vector m with
                            | eq_refl => v
                            end.
Proof.
Admitted.


(* 
cPVtc is a type-cast needed to formulate the lemma given below
*)

Lemma cPVtc : forall {n:nat} (v:vector n),  countPV v = countPV (filterV v).
Proof.
Admitted.

(* 
Use the lemmas proved above to show that filterV is idempotent
*)
 

Lemma filterV_idem: forall {n:nat} (v:vector n),
      filterV (filterV v) = match cPVtc v in _= m return vector m with
                            | eq_refl => filterV v
                            end.
Proof.
Admitted.

End filterV.
