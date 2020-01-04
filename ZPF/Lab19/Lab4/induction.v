Print le.


Lemma Z_le_n : forall n, le 0 n.
Proof.
induction n.
- constructor.
- constructor.
  assumption.
Qed.


Lemma le_S: forall n m, le n m -> le (S n) (S m).
Proof.
induction 1.
- constructor.
- constructor;assumption.
Qed.



Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).


Print pred.
Print Nat.pred.


Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
(*
  intros n E.
  induction E.
  - simpl; constructor.
  - simpl.
    assumption.
*)
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'. 

Qed.

Section A_dec.

Variable A : Type.
Variable eq_dec : forall (x y:A), {x=y}+{~ x=y}.

Locate "+".
Print sumbool.

Print list.

Fixpoint count_occ (x:A)(l:list A) :=
match l with
| nil => 0
| cons y l' => let n:= count_occ x l' in
             match eq_dec x y with
             | left _ => 1 + n
             | right _ => n
             end
end.


Lemma AtLeastOne: forall (x:A)(l:list A),count_occ x l > 0 -> l<> nil.
Proof.
intros x l.
destruct l.
- simpl.
  intros.
  inversion H.
- simpl.
  destruct (eq_dec x a); intros; congruence.
Qed.

End A_dec.


Check AtLeastOne.

Lemma nat_dec: forall (x y:nat), {x=y}+{~ x=y}.
Proof.
induction x; destruct y.
 - left; reflexivity.
 - right; congruence.
 - right; congruence.
 - destruct (IHx y).
   * left; congruence.
   * right; congruence.
Qed.

Check AtLeastOne nat nat_dec.








