Require Import Arith.
Require Import List.
Require Extraction.

Print nat.

Definition plus2 n := n+2.

Fixpoint factorial n := 
  match n with
    0 => 1
  | S m => n*fact m
end.

Eval compute in factorial 3.

Print list.

Check @nil nat.

Check @nil.

Check nil.

Check @cons.

Check cons 3 nil.

Check @cons nat 3 nil.


Fixpoint map (A B: Type)(f: A-> B) l := 
  match l with
    nil => nil
  | x::xs => (f x) ::  map A B f xs
end.

Check map.

Fixpoint mapi {A B: Type}(f: A-> B) l := 
  match l with
    nil => nil
  | x::xs => (f x) ::  mapi f xs
end.

Check mapi.


(* Types are first-class values *)

Fixpoint AddernatType (n:nat) := 
match n with 
  0 => nat
| (S k) => nat -> AddernatType k 
end.

Check AddernatType.


Fixpoint addernat (numargs : nat) (acc: nat): AddernatType numargs :=
match numargs with 
  0 => acc
| (S k) => fun next => addernat k (next + acc)
end.


Eval compute in (addernat 3 0 1 2 3).


(* Propositions and proofs are first-class values *)

Fixpoint len {A: Type} (l: list A) :=
  match l with
    nil => 0
  | x::xs => 1 + len xs
end.

Check len.


Lemma lenEqZero: forall A (l:list A), length l = 0 -> l = nil.
Proof.
intros.
destruct l.
* trivial.
* simpl in H.
  congruence.
Qed.

Print lenEqZero.


Print le.
Print "<=".
Print "<".
Print ">".

Lemma lenGeZero: forall A (l:list A), 0 <= length l. 
Proof.
intros.
induction l.
- simpl. trivial.
- simpl. constructor. trivial.
Qed.

Check lenGeZero.
Print lenGeZero. 


(* forall A (l:list A), 0 <= length l is a dependent type...*)


Inductive vector {T:Type} : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall n, T -> vector n -> vector (S n).

Check @Vcons.

Definition vhead {T:Type}{n:nat}(v:vector (S n)):T :=
match v with
  Vcons n h t => h
end. 


Extraction vector.
Extraction vhead.



(* congruence - decision procedure for ground equlities 
                with uninterpreted symbols *)

Lemma T (A:Type) (f:A -> A) (g: A -> A -> A) a b: 
a=(f a) -> (g b (f a))=(f (f a)) -> (g a b = f (g b a)) -> g a b = a.
Proof. 
intros.
congruence.
Qed.