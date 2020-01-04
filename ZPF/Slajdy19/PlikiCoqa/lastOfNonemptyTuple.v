Require Import Coq.Lists.List.
Set Implicit Arguments. 

(* Functional Dependent Types *)
(******************************)

(* In addition to defining types inductively, we can also define types
 * using definitions and fixpoints. A simple example is n-tuples.
 *)
Section tuple.
Variable T : Type.

Fixpoint tuple (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => T * tuple n
  end%type.


Check @fst.

Definition tuple_hd {a} : tuple (S a) -> T :=
  @fst _ _.

Print tuple_hd.

Definition tuple_tl {a} : tuple (S a) -> tuple a :=
  @snd _ _.



Definition grabtype n:Type := match n with O => unit | S n => T end.

Lemma lastL: forall (n: nat), tuple n ->  grabtype n.
Proof.
induction n.
- simpl; trivial.
- simpl.
  destruct n.
  + intro H; destruct H; assumption.
  + simpl in IHn. 
    intro.
    apply IHn.
    destruct X.
    destruct t0.
    split.
    exact t0.
    exact t1.
Defined.


Fixpoint lastF (n: nat): tuple n ->  grabtype n:=
match n as x return (tuple x -> grabtype x) with
| O => fun t => t
| S m => fun t (* tuple S m *) =>
   (match m as n1 return ((tuple n1 -> grabtype n1) -> T * tuple n1 -> T)
   with
   | 0 => fun _ H => let (t, _) := H in t
   | S n1 => fun IHn0 X => IHn0 (let (_,t0) := X in let (t1,t2) := t0 in (t1,t2))
   end) (lastF m) t
end.

Print lastL.
Print lastF.

Lemma last_eq: forall (n:nat)(t:tuple n), lastL n t = lastF n t.
Proof.
intros.
reflexivity.
Qed.

Lemma last_eqf: lastL = lastF.
Proof.
intros.
reflexivity.
Qed.


Definition lastOfNonempty (n:nat)(t:tuple (S n)):T := lastL (S n) t.

Variable a b c: T.

Definition f: tuple 1 := (a,tt).
Definition g: tuple 2 := (b, f).
Definition h: tuple 3 := (c, g).

Eval compute in (lastOfNonempty h).


End tuple.