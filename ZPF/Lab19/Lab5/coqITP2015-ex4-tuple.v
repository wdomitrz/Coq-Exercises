Require Import Coq.Lists.List.
Set Implicit Arguments. 

(* Functional Dependent Types *)
(******************************)

(* In addition to defining types inductively, we can also define types
 * using definitions and fixpoints. A simple example is n-tuples.
 *)
Section tuple.
Variable T : Type.

Check T.

Fixpoint tuple (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => T * tuple n
  end%type.

Check tuple.
Print tuple.
(*
End tuple.

Check tuple.
Print tuple.
*)

Variable aa bb:T.

Check (aa,(bb,tt)): tuple 2. 


Check @fst.

Locate "*".

Print prod.
Print "*"%type.

(* Exercise: Implement head, tail, and tappend for tuples. *)

(* You will need to convert this definition into a fixpoint. *)

Definition tappend (a b : nat) (va : tuple a) (vb : tuple b)
: tuple (a + b).
Admitted.

Arguments tappend {_ _} _ _.


(* [tuple n] is isomorphic to [vector T n].
 * Exercise: Write the two functions that witness this isomorphism
 * and prove that they form an isomorphism.
 *
 * I've repeated the definition of vector (from the lecture) here.
 *)

Inductive vector : nat -> Type :=
| Vnil : vector 0
| Vcons : forall {n}, T -> vector n -> vector (S n).

Definition tuple_to_vector {n} (t : tuple n) : vector n.
Admitted.

Definition vector_to_tuple {n} (t : vector n) : tuple n.
Admitted.

Theorem vector_tuple : forall n (v : vector n),
    tuple_to_vector (vector_to_tuple v) = v.
Admitted.

Theorem tuple_vector : forall n (t : tuple n),
    vector_to_tuple (tuple_to_vector t) = t.
Proof.
Admitted.

(* Exercise: Prove that tappend and vappend are related *)

Fixpoint vappend {a b} (va : vector a) (vb : vector b)
: vector (a + b) :=
  match va in vector a return vector (a + b) with
  | Vnil => vb
  | Vcons v vs => Vcons v (vappend vs vb)
  end.

Theorem vappend_tappend
: forall {a b} (va : vector a) (vb : vector b),
    vappend va vb =
    tuple_to_vector (tappend (vector_to_tuple va) (vector_to_tuple vb)).
Proof.
Admitted.


Theorem tappend_vappend 
: forall (a b : nat) (ta : tuple a) (tb : tuple b),
tappend ta tb = 
vector_to_tuple (vappend (tuple_to_vector ta) (tuple_to_vector tb)).
Proof.
Admitted.

End tuple.
