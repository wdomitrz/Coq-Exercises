Set Implicit Arguments.

Require Import List.
Require Import JMeq.




Scheme JMeq_rec_type := Induction for JMeq Sort Type.

(*
JMeq_rec_type.
     : forall (A : Type) (x : A)
         (P : forall (B : Type) (b : B), JMeq x b -> Type),
       P A x JMeq_refl -> forall (B : Type) (x0 : B) (j : JMeq x x0), P B x0 j
*)



Check JMeq_eq.

Check JMeq_ind.
Print JMeq_ind.

(*
JMeq_ind
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, JMeq x y -> P y
*)


Infix "==" := JMeq (at level 70, no associativity).


Lemma pairC: forall A B1 B2 (x:A)(y1:B1)(y2:B2), y1==y2 -> (x,y1) == (x, y2).
  intros until y2.
  intro Hy.
  rewrite Hy.
  reflexivity.
Qed.

Print pairC.


Definition Top_internal_JMeq_rew_r :=
fun (A : Type) (x : A) (B : Type) (b : B) (P : forall B0 : Type, B0 -> Type)
    (HC : P B b) (H : x == b) =>
  match H in (@JMeq _ _ B0 b0) return (P B0 b0 -> P A x) with
  | JMeq_refl => fun HC0 : P A x => HC0
  end HC. 


Check Top_internal_JMeq_rew_r.

Print Assumptions pairC.



Lemma pairC': forall A B1 (x:A)(y1 y2:B1), y1==y2 -> (x,y1) == (x, y2).
 intros.
  apply pairC.
  assumption.

Restart.
 intros.
  eapply JMeq_ind with (2:=H).
  reflexivity.

Restart.
  intros until y2.
  intro Hy.
  rewrite Hy.
  reflexivity.
Qed.

Print pairC'.

Print Assumptions pairC'.




Definition pairC'': forall A B1 (x:A)(y1 y2:B1), y1==y2 -> (x,y1) == (x, y2) := 
fun (A B1: Type) (x : A) (y1 y2: B1) (Hy : y1 == y2) =>
Top_internal_JMeq_rew_r (fun (B3 : Type) (y3 : B3) => (x, y3) == (x, y2))
  JMeq_refl Hy.

Print Assumptions pairC''.


