
Lemma and_comm: forall P Q, P/\Q -> Q /\ P.
Proof.
intros.
destruct H.
split.
 * assumption.
 * assumption.
Qed.

Print and_comm.



Lemma or_comm: forall P Q, P \/ Q -> Q \/ P.
Proof.
intros.
destruct H.
 * right. 
   assumption.
 * left;assumption.
Qed.

Print or_comm.

Print iff.

Lemma Iff_or_comm: forall P Q, P \/ Q <-> Q \/ P.
Proof.
intros.
split; apply or_comm.
Qed.


Print False.

Lemma FalseImpliesAny: False -> 2+2=5.
Proof.
intro.
destruct H.
Qed.


Lemma negations: forall P Q :Prop, ~P -> ~ ~ P -> Q.
Proof.
intros.
(*contradiction.*)
destruct H0.
assumption.
Qed.


Print ex.


(*Lemma is: @ex nat (fun x:nat => x+1 = 2).*)

Lemma istnieje1: exists x, x+1=2.
Proof.
exists 1.
simpl.
trivial.
Qed.

Lemma istnieje2: forall m n, (exists x, x+n = m) -> (n=m) \/ (exists k, m = S k).
Proof.
intros.
destruct H.
destruct x.
(*destruct x eqn:?.*)
* left.
  simpl in H.
  assumption.
* right.
  simpl in H.
  exists (x+n).
  symmetry.
  assumption.
Qed.
 

Definition Double_neg : Prop := forall P:Prop, ~~P -> P.

Definition Exm : Prop := forall P : Prop, P \/ ~P.

Definition Classical_impl : Prop := forall P Q:Prop, (P -> Q) -> ~P \/ Q.

Definition Peirce : Prop := forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition Not_forall_not_exists : Prop :=
           forall (A:Type)(P:A->Prop), ~(forall x:A, ~P x) -> ex P.


Lemma  Exm_Double_neg : Exm -> Double_neg.
Proof.
 unfold Double_neg.
 intros H P.
 destruct (H P) as [p | p'].
 - intro;assumption.
 - (* generalize p'. *)
 apply negations.
 assumption. 
(* intro H1.
 apply (negations P); assumption.*)
Qed.


