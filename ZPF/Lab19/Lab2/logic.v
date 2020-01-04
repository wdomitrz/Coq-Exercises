(* First, let us look at some example : *)

Lemma P3Q : forall P Q : Prop, (((P->Q)->Q)->Q) -> P -> Q.
Proof.
 intros P Q H p; apply H. 
 intro H0;apply H0;assumption. 
Qed.

Lemma triple_neg : forall P:Prop, ~~~P -> ~P.
Proof.
 intros P ;unfold not; apply P3Q.
Qed.


Lemma all_perm :
 forall (A:Type) (P:A -> A -> Prop),
   (forall x y:A, P x y) -> 
   forall x y:A, P y x.
Proof.
Admitted.

Lemma resolution :
 forall (A:Type) (P Q R S:A -> Prop),
   (forall a:A, Q a -> R a -> S a) ->
   (forall b:A, P b -> Q b) -> 
   forall c:A, P c -> R c -> S c.
Proof.
Admitted.


Lemma not_ex_forall_not : forall (A: Type) (P: A -> Prop),
                      ~(exists x, P x) <-> forall x, ~ P x.
Proof.
Admitted.


Lemma ex_not_forall_not : forall (A: Type) (P: A -> Prop),
                       (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
Admitted.


Lemma diff_sym : forall (A:Type) (a b : A), a <> b -> b <> a.
Proof.
Admitted.


Lemma fun_diff :  forall (A B:Type) (f : A -> B) (a b : A), 
                       f a <> f b -> a <> b.
Proof.
Admitted.
