Inductive list (A:Set) :Set := 
| Nil  : list A
| Cons : A -> list A -> list A.

Print list.
Check Nil.
Check Cons.

Check list_ind.

Arguments Nil [A].
Print Implicit Nil.
Check Nil.
Arguments Cons [A].
Check Cons.
Print Implicit Cons.


Check list_ind.


Fixpoint len {A} (l: list A) :=
  match l with
    Nil => 0
  | Cons _ xs => 1 + len xs
end.

Check len.

Fixpoint app {A} (l1 l2: list A) :=
  match l1 with
    Nil => l2
  | Cons x xs => Cons x (app xs l2)
end.

Check app.

Theorem length_app: forall A (l1 l2: list A), len (app l1 l2) = len l1 + len l2.
Proof.
induction l1.
- simpl.
  reflexivity.
- simpl.
  intros.
  (*specialize (IHl1 l2). rewrite IHl1. reflexivity.
  rewrite  IHl1; reflexivity.*)
  f_equal. apply IHl1.
Qed.


Inductive lista : Set -> Type :=
| Nila  : forall (A:Set), lista A
| Consa : forall (A:Set), A -> lista A -> lista A.

Check Consa.


Check lista_ind.


Fixpoint lena (A:Set) (l:lista A): nat :=
match l with
| Nila A => 0
| Consa A a t => 1 + lena A t  
end.

Lemma lenaGEO: forall (A:Set)(l:lista A), lena A l >=0.
Proof.
induction l.
simpl.
constructor.
simpl.
constructor.
auto.
Qed.


Lemma lenaGEOnat: forall (l:lista nat), lena nat l >=0.
Proof.
induction l.
simpl.
constructor.
simpl.
constructor.
auto.
Qed.

Print lenaGEOnat.









