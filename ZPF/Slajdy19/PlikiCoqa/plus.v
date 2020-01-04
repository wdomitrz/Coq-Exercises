Print nat.


Lemma plus_O_right: forall (n:nat), plus 0 n = n.
Proof.
intro.
reflexivity.
Qed.


Lemma plus_O_left: forall (n:nat), plus n O = n.
Proof.
induction n.
- reflexivity.
- simpl. 
  rewrite IHn.
  reflexivity.
Qed.

Print plus_O_left.
(*
apply (nat_ind (fun n => plus n O = n));
[reflexivity |
intros n IHn; simpl; rewrite IHn; reflexivity].
Qed.
*)

Check nat_rec.


Definition msucc := nat_rec (fun n:nat => nat) (S 0) (fun (n:nat)(x:nat) => S x).

Eval compute in msucc 0.
Eval compute in msucc (S(S 0)).

Definition mpred := nat_rec (fun n:nat => nat) 0 (fun (n:nat)(x:nat) => n).

Eval compute in mpred 0.
Eval compute in mpred (S(S 0)).

