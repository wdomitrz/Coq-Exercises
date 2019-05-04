(* First, let us look at some example : *)

Lemma P3Q : forall P Q : Prop, (((P->Q)->Q)->Q) -> P -> Q.
Proof.
 intros P Q H p.
 apply H. 
 intro H0. 
 apply H0. 
 assumption. 
Qed.

Lemma triple_neg : forall P:Prop, ~~~P -> ~P.
Proof.
  intros P.
  unfold not.
  apply P3Q.
Qed.


Lemma all_perm :
 forall (A:Type) (P:A -> A -> Prop),
   (forall x y:A, P x y) -> forall x y:A, P y x.
Proof.
  intros.
  apply (H y x).
Qed.

Lemma resolution :
 forall (A:Type) (P Q R S:A -> Prop),
   (forall a:A, Q a -> R a -> S a) ->
   (forall b:A, P b -> Q b) -> 
   forall c:A, P c -> R c -> S c.
Proof.
  intros.
  apply H.
  * apply H0.
    apply H1.
  * apply H2.
Qed.

Lemma not_ex_forall_not : forall (A: Type) (P: A -> Prop),
                      ~(exists x, P x) <-> forall x, ~ P x.
Proof.
  intros.
  split.
  * intro.
    intro.
    unfold not in H.
    unfold not.
    intro.
    apply H.
    exists x.
    assumption.
  * intro.
    unfold not.
    intro.
    unfold not in H.
    destruct H0.
    apply (H x).
    assumption.
Qed.

Lemma ex_not_forall_not : forall (A: Type) (P: A -> Prop),
                       (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
  intros.
  unfold not.
  destruct H.
  intro.
  apply (H0 x).
  assumption.
Qed.


Lemma diff_sym : forall (A:Type) (a b : A), a <> b -> b <> a.
Proof.
  intros.
  unfold not.
  unfold not in H.
  intro.
  apply H.
  symmetry.
  assumption.
Qed.

Lemma fun_diff :  forall (A B:Type) (f : A -> B) (a b : A), 
                       f a <> f b -> a <> b.
Proof.
  intros.
  unfold not.
  intro.
  unfold not in H.
  apply H.
  rewrite H0.
  trivial.
Qed.
