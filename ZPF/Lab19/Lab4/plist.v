Set Implicit Arguments.

Print sig.

(*
Define a kind of dependently typed lists, where a list’s type index
gives a lower bound on how many of its elements satisfy a particular
predicate. In particular, for an arbitrary set A and a predicate P over it:
*)

Section Plist.

Variable A : Type.
Variable P : A -> Prop.

(*
(a) Define an inductive type plist : nat → Type. Each plist n should be a list of As, 
where it is guaranteed that at least n distinct elements satisfy P. 
*)


Inductive plist : nat -> Type :=

(*
(b) Define a version of list concatenation that works on plists. The type
of this new function should express as much information as possible about 
the output plist.
*)


(*
(c) Define a function plistOut for translating plists to normal lists.
*)


(*
(d) Define a function plistIn for translating lists to plists. 
The type of plistIn should make it clear that the best bound on P 
-matching elements is chosen. 
You may assume that you are given a dependently typed function for 
deciding instances of P.
*)

Variable P_dec : forall x, {P x}+{~P x}.

Fixpoint countP (l : list A) := 
match l with 
| nil => O
| cons x l' => if P_dec x then S (countP l') else countP l'
end.

Locate "+".
Print sumbool.

(*
(e) Prove that, for any list ls, plistOut (plistIn ls) = ls. This should be 
the only part of the exercise where you use tactic-based proving.
*)

Lemma plistInOut : forall ls, plistOut (plistIn ls) = ls.
  
(*
(f) Define a function grab : ∀ n (ls : plist (S n)), sig P. That is, when 
given a plist guaranteed to contain at least one element satisfying P, 
grab produces such an element. The type family sig is the one we met 
earlier for sigma types (i.e., dependent pairs of programs and proofs), 
and sig P is extensionally equivalent to {x : A | P x }, though the latter 
form uses an eta-expansion of P instead of P itself as the predicate. 
*)

Print sig.


Definition grabtype n : Type := match n with O => unit | S _ => sig P end.





