Lemma ExampleCHI: forall A B C: Prop, (A -> B -> C) -> (A -> B) -> (A -> C).
(*intros.*)
intros A B C X Y Z.

apply X.

assumption.

apply Y.
assumption.
Qed.

Print ExampleCHI.


(* In natural deduction:


G, A |- A (axiom)


G, A |- B
-------------------- (-> intro) 
G |- A -> B


G |- A -> B      G |- A
-------------------------(-> elim)
G |- B

*)

Section Minimal_propositional_logic.
 Variables P Q R S : Prop.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
 Proof.
 intros H0 H1 H2 H3.
 apply H2.
 - apply H0.
   assumption.
 - apply H1; assumption.
 Qed.

Print diamond.

End Minimal_propositional_logic.

Print diamond.


Section Minimal_first_order_logic.
 Variables (A : Set)
   (P Q : A -> Prop)
   (R : A -> A -> Prop).

Theorem all_imp_dist :
  (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
 Proof.
 intros.
 apply H.
 apply H0.
 Qed.

Print all_imp_dist.

Theorem all_delta : (forall a b:A, R a b) -> forall a:A, R a a.
 Proof.
 intros.
 apply H.
 Qed.

End Minimal_first_order_logic.


Lemma P3Q : forall P Q : Prop, (((P->Q)->Q)->Q) -> P -> Q.
Proof.
 intros P Q H p; apply H. 
 intro H0;apply H0;assumption. 
Qed.

Print P3Q.
