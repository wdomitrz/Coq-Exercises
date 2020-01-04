Require Coq.Arith.Plus.
(** Dependent Inductive Types **)
(*******************************)

Section vectors.
  Variable T : Type.

  (* We can use dependent types to enrich types with their properties.
   * For example the type of 'lists with a given length'.
   * Traditionally, length-indexed lists are called 'vectors'.
   *)
  Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, T -> vector n -> vector (S n).

  Arguments Vcons {_} _ _.

  (** Let's define some more notation *)
  Local Notation "[|  |]" := Vnil.
  Local Notation "[|  x ; .. ; y  |]" := (@Vcons _ x (.. (@Vcons _ y Vnil) ..)).

  Section vector_examples.
    Variables a b c : T.

    Check [| |].
    Check [| a |].
    Check [| a ; b ; c |].
  End vector_examples.

  (* When we define dependent types inductively, we learn
   * information about the index (in this case the nat) when
   * we inspect the value.
   *
   * Coq's 'in'-clause allows us to express how the return
   * type depends on the indices
   *)

  Fixpoint append (l1 : list T) (l2 : list T) : list T.
  destruct l1.
  apply l2.
  apply cons. apply t. apply append. apply l1. apply l2.
  Defined.

  Require Import List.
  Theorem append_eq_app : append = @List.app T.
  reflexivity.
  Qed.

  (* 'in'-clause pattern matching *)
  Fixpoint vappend {n m : nat} (v1 : vector n) (v2 : vector m) {struct v1}
  : vector (n + m):=
    match v1 in vector l' return vector (l' + m) with
    | Vnil => v2
    | Vcons x xs => Vcons x (vappend xs v2)
    end.

  
  Section test2.
    Variables a b c : T.
    Eval compute in vappend [| a ; b |] [| c |].
  End test2.

  (* Can you implement appending a single element to the vector? *)
  Fixpoint vsnoc {n : nat} (x : T) (v : vector n)
  : vector (S n) :=
    match v
          in vector l'
          return vector (S l')
    with
    | Vnil => [| x |]
    | Vcons x' xs => Vcons x' (vsnoc x xs)
    end.

  Variables a b c : T.
  Eval compute in vsnoc c [| a ; b |].

  (* If we want to prove these two functions are related
   * in the obvious way, we run into a problem.
   *)
(*
  Theorem vappend_vsnoc : forall n x (v : vector n),
      vsnoc x v = vappend v [| x |].
*)


  (* The problem lies in the type of the theorem.
   * [vsnoc x v] has type [vector (S n)] while
   * [vappend v [| x |]] has type [vector (n + 1)].
   * While [S n = n + 1] is *provable* the two are
   * not definitionally equal.
   *
   * To state the above theorem, we need to use a
   * proof that [S n = n + 1] to 'cast'
   * [vappend v [| x |]] into the type [vector (S n)].
   * We can do this using dependent pattern matching
   * on equality types.
   *)
  Print eq.

  (* Dependent pattern matching on this type is quite
   * similar to dependent pattern matching on vectors.
   * Let's take a look by implementing [Vcast].
   *)
  Definition Vcast (n m : nat) (pf : n = m)
  : vector n -> vector m :=
    match pf with
    | eq_refl => fun x => x
    end.



  (* We can use dependent pattern matching on equality
   * proofs to state the associativity of [vappend].
   *)
  Theorem vappend_assoc
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc
      = match Plus.plus_assoc a b c in @eq _ _ X return vector X with
        | eq_refl => vappend va (vappend vb vc)
        end.
  Proof.
    induction va.
    - simpl. admit.
    - simpl. intros. rewrite IHva.
      admit.
  Abort.




  (* Everything will work out if we have a transparent definition of
   * plus_assoc.
   *)
  Lemma plus_assoc_trans : forall n m p : nat, n + (m + p) = n + m + p.
  Proof.
    induction n.
    { reflexivity. }
    { simpl. intros. f_equal. apply IHn. }
  Defined.

  Theorem vappend_assoc
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc
      = match plus_assoc_trans a b c in _ = X return vector X with
        | eq_refl => vappend va (vappend vb vc)
        end.
  Proof.
    induction va.
    - simpl. reflexivity.
    - simpl. intros. rewrite IHva.
      clear IHva.
      generalize (plus_assoc_trans n b0 c0).
      destruct e. simpl. reflexivity.
  Qed.







  (* In some cases, the value of the index guarantees that
   * certain cases are not possible. For example, getting
   * the first element of a non-empty vector.
   *
   * Coq still requires that we address all the cases.
   *)
  Definition vhd {n : nat} (v : vector (S n)) : T :=
    match v
          in vector l'
          return match l' return Type with
                 | 0 => unit
                 | S _ => T
                 end
    with
    | Vnil => tt
    | Vcons x' xs' => x'
    end.

  (* The technique above shows how to express "impossible"
   * cases by making the 'return' clause return easy to
   * construct types in those cases.
   *
   * Can you implement the tail function for vectors?
   *)

Print pred.

(* Fill the definition:

Definition vtl {n : nat} (v : vector (S n)) : vector n :=
*)



  (* Understanding a dependent pattern matching is important
   * when it comes to implementing functions/proving theorems
   * about eta-expansion (as well as many other properties).
   *)

(* Fill the definition:

  Definition vector_eta n (v : vector (S n))
  : v = Vcons (vhd v) (vtl v):=
*)


  (* Note that here, we need to pass [v'] from the outside so
   * that learning additional information about [n'] updates
   * refines the type of [v'].
   *)

  (* Can you use a similar strategy to prove that [Vcons]
   * is injective?
   *
   * Note that [inversion] does not help here due to the
   * dependency.
   *)

(*  Fill the definition:

Definition Vcons_inj n (a b : T) (v:vector n) :  forall (v' : vector n),
      Vcons a v = Vcons b v' -> a = b /\ v = v':=
*)


  (************************** END LECTURE *****************************)

   (* More functions *)
  (******************)

  (* To get more of a flavor of using dependent pattern
   * matching, try implementing some more functions and
   * verifying properties about them.
   *)


(* Fill the definition:

  Fixpoint vrev {n : nat} (v : vector n)
  : vector n :=
 *)


  Fixpoint vlength {n : nat} (v : vector n) : nat:= 
  match v with
  | Vnil => 0
  | Vcons _ l => 1+ vlength l
  end.

  Theorem vlength_is_length
  : forall n (v : vector n),
      vlength v = n.
  Proof.
Admitted.

Check plus_n_O.

Lemma plus_n_O_trans : forall n : nat, n = n + 0.
Proof.
induction n.
- simpl. trivial.
- simpl. f_equal. trivial.
Defined.

Print plus_n_O_trans. 

  Theorem vappend_Vnil
  : forall a (va : vector a),
      match plus_n_O_trans a in _ = X return vector X with
      | eq_refl => va
      end = vappend va [| |].
  Proof. Admitted.

 
Check plus_n_Sm.

Lemma plus_n_Sm_trans: forall n m : nat, S (n + m) = n + S m.
Proof.
induction n.
- simpl. trivial.
- simpl.
  intro.
  f_equal.
  apply IHn.
Defined.




  Theorem vsnoc_append
  : forall b a (va : vector a) (vb : vector b) x,
      vsnoc x (vappend va vb) =
      match (*n+Sm = S(n+m)*) eq_sym (plus_n_Sm_trans a b) in _ = X return vector X with
      | eq_refl => vappend va (vsnoc x vb)
      end.
  Proof. Admitted.


Lemma plus_comm_trans:  forall n m : nat, n + m = m + n.
Proof.
induction n.
- simpl.
  apply plus_n_O_trans.
- simpl.
  intro.
  symmetry in IHn.
  destruct (IHn m).
  apply plus_n_Sm_trans.
Defined.

    
  Theorem vrev_append
    : forall a b (va : vector a) (vb : vector b),
      vrev (vappend va vb)
      = match eq_sym (plus_comm_trans a b) in _ = X return vector X with
        | eq_refl => vappend (vrev vb) (vrev va)
        end.
  Proof.Admitted.



End vectors.


(*
destruct H: a=b

informally makes substitution "b mapsto a" in the goal

If the goal is:

f: n, vector n -> C, n:nat, v :vector n |- t =  f (n+0) (vappend v Vnil)

then "n+0 mapsto n" (the result of destruct H:n=n+0) makes the term nontypable.

This is why sometimes destruct does not succeed, 

*)
