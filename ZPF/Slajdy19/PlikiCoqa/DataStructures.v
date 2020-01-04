Set Implicit Arguments.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

(*
  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls in ilist k return (fin k -> A) with
      | Nil => fun idx =>
        match idx in fin n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ => tt
        end 
      | Cons x ls' => fun idx =>
        match idx in fin n' return A with
          | First _ => x
          | Next idx' => get ls' idx'
        end 
    end.


*)


  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls (*in ilist k return (fin k -> A)*) with
      | Nil => fun idx =>
        match idx in fin n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ => tt
        end 
      | Cons x ls' => fun idx =>
        match idx in fin n' return (fin (pred n') -> A) -> A with
          | First _ => fun _ => x
          | Next idx' => fun get_ls' => get_ls' idx'
        end (get ls')
    end.


End ilist.

Check Cons.
Arguments Cons [A n].
Arguments Nil [A].


Check Nil.

Check (Cons 2 Nil).

Check (Cons 1 (Cons 2 Nil)).


Arguments First [n].
Arguments Next [n].

Check (get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next First)).


Require Import List.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  (* EX: Define a type [hlist] indexed by a [list A], where the type of each element is determined by running [B] on the corresponding element of the index list. *)

  (** We parameterize our heterogeneous lists by a type [A] and an [A]-indexed type [B].%\index{Gallina terms!hlist}% *)

(* begin thide *)
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  (** We can implement a variant of the last section's [get] function for [hlist]s.  To get the dependent typing to work out, we will need to index our element selectors (in type family [member]) by the types of data that they point to.%\index{Gallina terms!member}% *)

(* end thide *)
  (* EX: Define an analogue to [get] for [hlist]s. *)

(* begin thide *)
  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  (** Because the element [elm] that we are "searching for" in a list does not change across the constructors of [member], we simplify our definitions by making [elm] a local variable.  In the definition of [member], we say that [elm] is found in any list that begins with [elm], and, if removing the first element of a list leaves [elm] present, then [elm] is present in the original list, too.  The form looks much like a predicate for list membership, but we purposely define [member] in [Type] so that we may decompose its values to guide computations.

     We can use [member] to adapt our definition of [get] to [hlist]s.  The same basic [match] tricks apply.  In the [HCons] case, we form a two-element convoy, passing both the data element [x] and the recursor for the sublist [mls'] to the result of the inner [match].  We did not need to do that in [get]'s definition because the types of list elements were not dependent there. *)

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
      | HNil => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => B elm
                                          | _ :: _ => unit
                                        end) with
          | HFirst _ => tt
          | HNext _ _ => tt
        end
      | HCons e mls' => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => Empty_set
                                          | x' :: ls'' =>
                                            B x' -> (member ls'' -> B elm)
                                            -> B elm
                                        end) with
          | HFirst _ => fun e' _ => e'
          | HNext _ mem' => fun _ get_mls' => get_mls' mem'
        end e (hget mls')
    end.
(* end thide *)

Check hget.
End hlist.


Check hget.
Check member.
Print member.

Definition someTypes :list Set :=nat :: bool :: nil.

Check hlist.
Check HCons.

Arguments HCons [A B x ls].
Arguments HNil [A B].

Example someValues: hlist (fun T:Set => T) someTypes :=
HCons 5 (HCons true HNil).


Inductive type:Set :=
| Unit : type
| Arrow : type -> type -> type.

Inductive exp: list type -> type -> Set :=
| Const : forall ts, exp ts Unit
| Var : forall ts t, member t ts -> exp ts t
| App : forall ts dom ran, exp ts (Arrow dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (Arrow dom ran).

Fixpoint typeDenote (t:type) : Set :=
match  t with
| Unit => unit
| Arrow dom ran => typeDenote dom -> typeDenote ran
end.

Fixpoint expDenote ts t (e:exp ts t): hlist typeDenote ts -> typeDenote t :=
match e in exp ts t return hlist typeDenote ts -> typeDenote t with 
| Const _ => fun _=> tt
| Var mem => fun s => hget s mem
| App e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
| @Abs ts0 dom ran e' => fun (s: hlist typeDenote ts0) (d: typeDenote dom) 
     => @expDenote (dom::ts0) ran e' (HCons d s)
end.


Arguments Const [ts].
Arguments HFirst [A elm ls].
Arguments HNext [A elm x ls].

Eval simpl in expDenote Const HNil.
Eval simpl in expDenote (Abs (dom:=Unit)(Var HFirst)) HNil.
Eval simpl in expDenote (Abs (dom:=Unit)(Abs (dom:=Unit) (Var (HNext HFirst)))) HNil.


Print unit.
Print Unit.






