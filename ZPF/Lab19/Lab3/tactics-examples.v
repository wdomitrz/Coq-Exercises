

Print plus.

Check plus.

Locate "+". 


(*
tactic try
command SearchPattern
*)

Lemma plus_lew: forall n m, plus n (S m) = plus (S n) m.
Proof.
induction n; try reflexivity.
SearchPattern (_ = _  + S _).
intro.
rewrite <- plus_n_Sm. (* This is almost the same lemma that we prove *)
simpl.
trivial.
Qed.


(* 
tactic injection
*)

Lemma inj_S : forall x y, S x = S y -> x = y.
Proof.
 intros.
(* congruence.*) 
 injection H.
 intro.
 auto. 
Qed.

(* 
tactic f_equal
*)

Lemma fun_S : forall x y, x = y -> S x = S y.
Proof.
 intros.
(* congruence.*)
 f_equal.
 auto.
Qed.


(* 
tactic pose proof
*)

Print pred.

Lemma pred_plus_1 : (forall n, plus n 1 = plus 1 n) -> forall k, pred (plus k 1) = k.  
Proof.
intros.
specialize (H k).
Undo.
pose proof (H k) as H1.
rewrite H1.
simpl.
auto.
Qed.

(* 
tactic assert
*)

Print pred.

Lemma pred_plus_2 : forall k, pred (plus k 1) = k.  
Proof.
intros.
assert (forall n, plus n 1 = plus 1 n).
- induction n; auto.
  simpl.
  rewrite IHn.
  auto.
- rewrite H.
  auto.
Qed.


