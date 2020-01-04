Set Implicit Arguments.

Inductive JMeq (A : Type) (x : A) : forall B : Type, B -> Prop :=
    JMeq_refl : JMeq x x.


Check JMeq_ind.

Check eq_rect.

Infix "==" := JMeq (at level 70, no associativity).

Lemma eqJMeq: forall (A:Type)(x y:A), x=y -> x==y.
intros.
rewrite H.
reflexivity.
Qed.


Definition UIP_refl' (A:Type)(x:A)(pf:x=x) : pf == eq_refl x :=
match pf as pf' in _= x' return (pf' == eq_refl x') with
 | eq_refl => JMeq_refl _
end.

(* Not provable in Coq *)
Definition UIP_refl (A:Type)(x:A)(pf:x=x) :pf = eq_refl x :=
match pf as pf' in _ = x' return (pf' = eq_refl _) with
 | eq_refl => eq_refl _
end.
