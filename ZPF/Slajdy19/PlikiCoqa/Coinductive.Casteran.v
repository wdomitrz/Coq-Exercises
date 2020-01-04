(* Lazy lists . P. Casteran after Eduardo Gimenez *)
(**************************************************)

Require Import Arith.
Require Import Setoid. 

Set Implicit Arguments.

CoInductive LList (A:Type) : Type :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil [A].

Check (LCons 1 (LCons 2 (LCons 3 LNil))).

Definition isEmpty (A:Type) (l:LList A) : Prop :=
  match l with
  | LNil => True
  | LCons a l' => False
  end.


Definition LHead (A:Type) (l:LList A) : option A :=
  match l with
  | LNil => None 
  | LCons a l' => Some a
  end.



Definition LTail (A:Type) (l:LList A) : LList A :=
  match l with
  | LNil => LNil 
  | LCons a l' => l'
  end.


Fixpoint LNth (A:Type) (n:nat) (l:LList A) {struct n} : 
 option A :=
  match l with
  | LNil => None 
  | LCons a l' => match n with
                  | O => Some a
                  | S p => LNth p l'
                  end
  end.



Eval compute in (LNth 2 (LCons 4 (LCons 3 (LCons 90 LNil)))).



CoFixpoint from (n:nat) : LList nat := LCons n (from (S n)).

Definition Nats : LList nat := from 0.


Eval simpl in (isEmpty Nats).

Eval cbv beta delta in (isEmpty Nats).

Eval simpl in (from 3).

Eval compute in (from 3).

Eval simpl in (LHead (LTail (from 3))).

Eval simpl in (LNth 19 (from 17)).



CoFixpoint forever (A:Type) (a:A) : LList A 
            := LCons a (forever a).

CoFixpoint LAppend (A:Type) (u v:LList A) : LList A :=
  match u with
  | LNil => v
  | LCons a u' => LCons a (LAppend u' v)
  end.

Eval compute in (LNth 123 (LAppend (forever 33) Nats)).


Eval compute in
  (LNth 123 (LAppend (LCons 0 (LCons 1 (LCons 2 LNil))) Nats)).


CoFixpoint general_omega (A:Type) (u v:LList A) : LList A :=
  match v with
  | LNil => u
  | LCons b v' =>
      match u with
      | LNil => LCons b (general_omega v' (LCons b v'))
      | LCons a u' => LCons a (general_omega u' (LCons b v'))
      end
  end.

Definition omega (A:Type) (u:LList A) : LList A 
             := general_omega u u.


Eval simpl in
  (LNth 3
     (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))).

Eval simpl in (forever 33).

Eval simpl in (LAppend (forever 33) (forever 69)).

Eval simpl in (LNth 15 (LAppend (forever 33) (forever 69))).

Definition LList_decompose (A:Type) (l:LList A) : LList A :=
  match l with
  | LNil => LNil
  | LCons a l' => LCons a l'
  end.

Eval simpl in (LList_decompose (forever 33)).


Lemma LList_decomposition : 
 forall (A:Type) (l:LList A), l = LList_decompose l.
Proof.
 intros A l.
 destruct l.
 trivial.
 trivial. 
Qed.


Definition Squares_from :=
  let sqr := fun n:nat => n * n in
  (cofix F : nat -> LList nat 
    := fun n:nat => LCons (sqr n) (F (S n))).

Require Import List.

Eval simpl in ((1 :: 2 :: nil) ++ 3 :: 4 :: nil).

Eval simpl in
  (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil))).


Lemma LAppend_one :
 forall (A:Type) (a:A) (u v:LList A),
   LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
 simpl in |- *.
Abort.

Eval simpl in
  (LList_decompose
     (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil )))).


Fixpoint LList_decompose_n (A:Type) (n:nat) 
            (l:LList A) {struct n} : LList A :=
  match n with
  | O => l
  | S p =>
      match LList_decompose l with
      | LNil => LNil
      | LCons a l' => LCons a (LList_decompose_n p l')
      end
  end.

Eval simpl in
  (LList_decompose_n 4
     (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))).

Eval simpl in (LList_decompose_n 12 Nats).

Eval simpl in (LList_decompose_n 5 (omega (LCons 1 (LCons 2 LNil)))).

Eval simpl in (LList_decompose (LAppend (LNil (A:=nat)) LNil)).

Eval simpl in (LList_decompose (LAppend LNil (forever 33))).

Eval simpl in (LList_decompose (LAppend (forever 33) (forever 69))).

Lemma LList_decomposition_n :
 forall (A:Type) (n:nat) (l:LList A), l = LList_decompose_n n l.
Proof.
 intros A n; elim n.  
 - intro l; case l; try reflexivity.
 - intros n0 H0 l; case l; try trivial.
   intros a l0; simpl in |- *; rewrite <- H0; trivial.
Qed.

Check trans_equal.
Print trans_equal.

Ltac LList_unfold term := 
     apply trans_equal with
     (1 := LList_decomposition term).

Print eq_trans.

Lemma LAppend_LNil : 
   forall (A:Type) (v:LList A), LAppend LNil v = v.
Proof.
 intros A v.
 LList_unfold (LAppend LNil v).
 case v; simpl in |- *; reflexivity.
Qed.

Lemma LAppend_LCons :
  forall (A:Type) (a:A) (u v:LList A),
    LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
 intros A a u v.
 LList_unfold (LAppend (LCons a u) v).
 case v; simpl in |- *; reflexivity.
Qed.
 
Hint Rewrite  LAppend_LNil LAppend_LCons : llists.

Lemma from_unfold : forall n:nat, from n = LCons n (from (S n)).
Proof.
 intro n.
 LList_unfold (from n).
 simpl in |- *; trivial.
Qed.


Lemma forever_unfold : forall (A:Type) (a:A), forever a = LCons a (forever a).
Proof.
 intros A a; LList_unfold (forever a); trivial.
Qed.


Inductive Finite (A:Type) : LList A -> Prop :=
  | Finite_LNil : Finite LNil
  | Finite_LCons : forall (a:A) (l:LList A), Finite l -> Finite (LCons a l).

Hint Resolve Finite_LNil Finite_LCons: llists.

Remark one_two_three : Finite (LCons 1 (LCons 2 (LCons 3 LNil))).
Proof.
 repeat constructor.
Qed.

Theorem Finite_of_LCons :
 forall (A:Type) (a:A) (l:LList A), Finite (LCons a l) -> Finite l.
Proof.
 intros A a l H. inversion H; assumption.
Qed.


Theorem LAppend_of_Finite :
 forall (A:Type) (l l':LList A),
   Finite l -> Finite l' -> Finite (LAppend l l').
Proof.
 intros A l l' H.
 induction H; autorewrite with llists  using auto with llists.
Qed.


Lemma general_omega_LNil :
 forall (A:Type) (u:LList A), general_omega u LNil = u.
Proof.
 intros A u.
 LList_unfold (general_omega u LNil).
 case u; simpl in |- *; auto.
Qed.

Lemma omega_LNil : forall A:Type, omega (@LNil A) = LNil.
Proof.
 intro A; unfold omega in |- *; apply general_omega_LNil. 
Qed.

Lemma general_omega_LCons :
 forall (A:Type) (a:A) (u v:LList A),
   general_omega (LCons a u) v = LCons a (general_omega u v).
Proof.
 intros A a u v.
 LList_unfold (general_omega (LCons a u) v); case v; simpl in |- *; auto.
 rewrite general_omega_LNil.
 trivial.
Qed.



Lemma general_omega_LNil_LCons :
 forall (A:Type) (a:A) (u:LList A),
   general_omega LNil (LCons a u) = LCons a (general_omega u (LCons a u)).
Proof.
 intros A a u; LList_unfold (general_omega LNil (LCons a u)); trivial.
Qed.

Hint Rewrite  omega_LNil general_omega_LNil general_omega_LCons : llists.

Lemma general_omega_shoots_again :
 forall (A:Type) (v:LList A), general_omega LNil v = general_omega v v.
Proof.
 simple destruct v. 
 trivial.
 intros; autorewrite with llists  using trivial.
 rewrite general_omega_LNil_LCons.
 trivial.
Qed.


Lemma general_omega_of_Finite :
 forall (A:Type) (u:LList A),
   Finite u ->
   forall v:LList A, general_omega u v = LAppend u (general_omega v v).
Proof.
 simple induction 1.
 intros; autorewrite with llists  using auto with llists. 
 rewrite general_omega_shoots_again.
 trivial.
 intros; autorewrite with llists  using auto.
 rewrite H1; auto.
Qed.


Theorem omega_of_Finite :
 forall (A:Type) (u:LList A), Finite u -> omega u = LAppend u (omega u).
Proof.
 intros; unfold omega in |- *.
 apply general_omega_of_Finite; auto.
Qed.
  

CoInductive Infinite (A:Type) : LList A -> Prop :=
    Infinite_LCons :
      forall (a:A) (l:LList A), Infinite l -> Infinite (LCons a l).

Hint Resolve Infinite_LCons: llists.

Check from_unfold.


(* manual proof (look at from_Infinite) *)
Definition F_from :
  (forall n:nat, Infinite (from n)) -> forall n:nat, Infinite (from n).
 intros H n.
 rewrite (from_unfold n). 
 constructor.
 apply H.  
Defined.

Print F_from.
Check F_from.


Theorem from_Infinite_V0 : forall n:nat, Infinite (from n).
Proof 
(cofix H : forall n:nat, 
Infinite (from n) := F_from H).

(* end of manual proof *)

Check from_unfold.
(*from_unfold
     : forall n : nat, from n = LCons n (from (S n))
*)

(* direct  proof *)
Lemma from_Infinite : forall n:nat, Infinite (from n).
Proof.
 cofix H.
Show Proof.
 intro n. 
Show Proof.
rewrite (from_unfold n).
Show Proof.
Check eq_ind_r.
 constructor. 
 apply H.
Qed.


Print from_Infinite.


Lemma from_Infinite_buggy : forall n:nat, Infinite (from n).
Proof.
 cofix H.
 auto with llists.
(*Guarded.*)
(*Qed.*)
Abort.

Lemma from_Infinite_saved : forall n:nat, Infinite (from n).
Proof.
 cofix H.
 auto with llists.
 Undo.
 intro n; rewrite (from_unfold n).
 constructor.
 auto.  
Qed.

Lemma forever_infinite : forall (A:Type) (a:A), Infinite (forever a).
Proof.
 intros A a; cofix H.
 rewrite (forever_unfold a).
 auto with llists.
Qed.


Lemma LNil_not_Infinite : forall A:Type, ~ Infinite (@LNil A).
Proof.
 intros A H.  inversion H. 
Qed.

Lemma Infinite_of_LCons :
  forall (A:Type) (a:A) (u:LList A), Infinite (LCons a u) -> Infinite u.
Proof.
  intros A a u H; inversion H; auto.
Qed.
 
Lemma LAppend_of_Infinite :
  forall (A:Type) (u:LList A),
    Infinite u -> forall v:LList A, Infinite (LAppend u v).
Proof.
 intro A; cofix H.
 simple destruct u.
 intro H0; inversion H0.
 intros a l H0 v.
 autorewrite with llists  using auto with llists. 
 split.
 apply H.
 inversion H0; auto.
Qed.

Lemma Finite_not_Infinite :
 forall (A:Type) (l:LList A), Finite l -> ~ Infinite l.
Proof.
 simple induction 1.
 unfold not in |- *; intro H0; inversion_clear H0. 
 unfold not at 2 ; intros a l0 H1 H2 H3.
 inversion H3; auto.
Qed.


Lemma Infinite_not_Finite :
  forall (A:Type) (l:LList A), Infinite l -> ~ Finite l.
Proof.
 unfold not in |- *; intros.
 absurd (Infinite l); auto.
 apply Finite_not_Infinite; auto.
Qed.

Lemma Not_Finite_Infinite :
  forall (A:Type) (l:LList A), ~ Finite l -> Infinite l.
Proof.
 cofix H.
 simple destruct l.
 intros; absurd (Finite (@LNil A)); auto with llists.
 split.
 apply H; unfold not in |- *; intro H1.
 apply H0; auto with llists.
Qed.

Lemma general_omega_infinite :
 forall (A:Type) (a:A) (u v:LList A), Infinite (general_omega v (LCons a u)).
Proof.
 intros A a; cofix H.
 simple destruct v.
 rewrite general_omega_LNil_LCons; split; auto.
 intros a0 l. 
 autorewrite with llists  using auto with llists.
Qed.

Lemma omega_infinite :
  forall (A:Type) (a:A) (l:LList A), Infinite (omega (LCons a l)).
Proof.
 unfold omega in |- *. 
 intros; apply general_omega_infinite.
Qed.

Lemma Lappend_of_Infinite_0 :
 forall (A:Type) (u:LList A), Infinite u -> forall v:LList A, u = LAppend u v.
Proof.
 simple destruct u.
 intro H; inversion H.
 intros a l H; inversion H; intros.
 rewrite LAppend_LCons.
 cut (l = LAppend l v).
 simple induction 1; auto.
Abort.


CoInductive bisimilar (A:Type) : LList A -> LList A -> Prop :=
  | bisim0 : bisimilar LNil LNil
  | bisim1 :
      forall (a:A) (l l':LList A),
        bisimilar l l' -> bisimilar (LCons a l) (LCons a l').

 Hint Resolve bisim0 bisim1: llists.

Lemma bisimilar_inv_1 :
 forall (A:Type) (a a':A) (u u':LList A),
   bisimilar (LCons a u) (LCons a' u') -> a = a'.
Proof.
 intros A a a' u u' H.
 inversion H; trivial.
Qed.

Lemma bisimilar_inv_2 :
 forall (A:Type) (a a':A) (u u':LList A),
   bisimilar (LCons a u) (LCons a' u') -> bisimilar u u'.
Proof.
 intros A a a' u u' H.
 inversion H; auto.
Qed.

Require Import Relations.

Lemma bisimilar_refl : forall A:Type, reflexive _ (@bisimilar A).
Proof.
 unfold reflexive in |- *; cofix H.
 intros A u; case u; [ left | right ].
 apply H.
Qed.

Hint Resolve bisimilar_refl: llists.

Lemma bisimilar_sym : forall A:Type, symmetric _ (@bisimilar A).
Proof.
 unfold symmetric in |- *; intro A; cofix H.
 simple destruct x; simple destruct y.
 auto with llists.
 intros a l H0; inversion H0.
 intro H0; inversion H0.
 intros a0 l0 H1; inversion H1. 
 right; auto.
Qed.
 
Lemma bisimilar_trans : forall A:Type, transitive _ (@bisimilar A).
Proof.
 unfold transitive in |- *; intro A; cofix H.
 simple destruct x.
 simple destruct y.
 auto.
 intros a l w H0; inversion H0.
 simple destruct y.
 intros w H0; inversion H0.
 intros a0 l0 w H0 H1.
 inversion_clear H1.
 inversion_clear H0.
 right.
 eapply H; eauto.
Qed.

Theorem bisimilar_equiv : forall A:Type, equiv _ (@bisimilar A).
Proof.
 split.
 apply bisimilar_refl.
 split. 
 apply bisimilar_trans.
 apply bisimilar_sym.
Qed.

(* new 8.2 *)

Add Parametric Relation (A:Type): (@LList A) (@bisimilar A)
  reflexivity proved by (@bisimilar_refl A)
symmetry proved by (@bisimilar_sym A)
transitivity proved by (@bisimilar_trans A)
   as bisim_rel.  



(* new 8.2 *)

Add Parametric Morphism A : (@LHead A)  with signature (@bisimilar A)==> (@Logic.eq (option A)) as LHead_m.
Proof.
 intros  l;case l.
 inversion 1;firstorder.
 inversion 1.
 simpl;tauto.
Qed.


Add Parametric  Morphism A : (@LTail A) 
  with signature (@bisimilar A)==> (@bisimilar A) as LTail_m.
Proof.
 intros  l;case l.
 inversion 1;simpl;constructor. 
 inversion 1.
 simpl. 
auto. 
Qed.


Add Parametric Morphism A : (@LNth   A)
 with signature (@Logic.eq nat) ==> (@bisimilar A)==> (@Logic.eq (option A)) 
as LNth_m.
Proof.

 simple induction y.
 simple destruct x; simple destruct y0.
 intros; simpl in |- *; trivial.
 intros a l H; inversion H.
 intro H; inversion H.
 intros a0 l0 H; inversion H; simpl in |- *; trivial.
 simple destruct x; simple destruct y0.
 intros; simpl in |- *; trivial.
 intros a l H0; inversion H0.
 intro H0; inversion H0.
 simpl in |- *; auto.
 intros a0 l0 H0; inversion_clear H0.
 auto.
Qed.

Check LNth_m.




Theorem bisimilar_of_Finite_is_Finite :
 forall (A:Type) (l:LList A),
   Finite l -> forall l':LList A, bisimilar l l' -> Finite l'.
Proof.
 simple induction 1.
 simple destruct l'.
 auto with llists.
 intros a l0 H1; inversion H1.
 simple destruct l'.
 intro H2; inversion H2.
 intros a0 l1 H2; inversion H2; auto with llists.
Qed.


Add Parametric Morphism A : (@Finite A) 
 with signature (@bisimilar A) ==> iff as Finite_m.
Proof. 
 split; intros; eapply bisimilar_of_Finite_is_Finite;eauto.
 rewrite H.
 reflexivity.
Qed.



Theorem bisimilar_of_Infinite_is_Infinite :
 forall (A:Type) (l:LList A),
   Infinite l -> forall l':LList A, bisimilar l l' -> Infinite l'.
Proof.
 intro A; cofix H.
 simple destruct l.
 intro H0; inversion H0.
 simple destruct l'.
 intro H1; inversion H1.
 split.
 apply H with l0.
 apply Infinite_of_LCons with a.
 assumption.
 inversion H1; auto.
Qed.

(* new 8.2 *)

Add Parametric Morphism A : (@Infinite A) 
with signature (@bisimilar A) ==> Logic.iff as 
  Infinite_m.
  split;
  intro;eapply bisimilar_of_Infinite_is_Infinite;eauto. 
  symmetry;assumption. 
Qed.



Theorem bisimilar_of_Finite_is_eq :
 forall (A:Type) (l:LList A),
   Finite l -> forall l':LList A, bisimilar l l' -> l = l'.
Proof.
 simple induction 1.
 intros l' H1; inversion H1; auto.
 simple destruct l'.
 intro H2; inversion H2.
 intros a0 l1 H2; inversion H2; auto with llists.
 rewrite (H1 l1); auto.
Qed.



      

Lemma bisimilar_LNth :
 forall (A:Type) (n:nat) (u v:LList A), bisimilar u v -> LNth n u = LNth n v.
Proof.
 intros A n u v E.
 rewrite E.
 trivial.
Qed.


(* New 8.2 : the right to left implication uses setoids *)

Lemma LNth_bisimilar :
 forall (A:Type) (u v:LList A),
   (forall n:nat, LNth n u = LNth n v) <-> bisimilar u v.
Proof.
 intro A.
 split.
 generalize u v;
 cofix H.
 simple destruct u0; simple destruct v0.
 left.
 intros a l H1.
 generalize (H1 0); discriminate 1.
 intro H1.
 generalize (H1 0); discriminate 1.
 intros.
 generalize (H0 0); simpl in |- *.
 injection 1.
 simple induction 1.
 right.
 Guarded.
 apply H.
 intro n.
 generalize (H0 (S n)).
 simpl in |- *. 
 auto.

 intros E n;rewrite E.
 trivial.
Qed.



Lemma LAppend_assoc :
 forall (A:Type) (u v w:LList A),
   bisimilar (LAppend u (LAppend v w)) (LAppend (LAppend u v) w).
Proof.
 intro A; cofix H.
 simple destruct u; intros; autorewrite with llists using auto with llists.
 apply bisimilar_refl.
Qed.

(*intros.
Focus 2.
intros.
cut (LAppend (LCons a l) (LAppend v w) = LCons a (LAppend l (LAppend v w))).
cut (LAppend (LCons a l) v = LCons a (LAppend l v)).
cut (LAppend (LCons a (LAppend l v)) w = LCons a (LAppend (LAppend l v) w)).
intros.
rewrite H2; rewrite H1; rewrite H0.
constructor.
auto.
Guarded.
apply LAppend_LCons.
apply LAppend_LCons.
apply LAppend_LCons.

cut (LAppend LNil v = v); try apply LAppend_LNil.
cut (LAppend LNil (LAppend v w) = LAppend v w); try apply LAppend_LNil.
intros.
rewrite H1; rewrite H0.
apply bisimilar_refl.
Qed.

*)


Lemma LAppend_of_Infinite_eq :
  forall (A:Type) (u:LList A),
    Infinite u -> forall v:LList A, bisimilar u (LAppend u v).
Proof.
 intro A; cofix H.
 simple destruct u.
 intro H0; inversion H0.
 intros; autorewrite with llists using auto with llists. 
 right.
 apply H.
 apply Infinite_of_LCons with a.
 assumption.
Qed.

Lemma general_omega_lappend :
  forall (A:Type) (u v:LList A),
    bisimilar (general_omega v u) (LAppend v (omega u)).
Proof.
 intro A; cofix H.
 simple destruct v.
 autorewrite with llists  using auto with llists.
 rewrite general_omega_shoots_again.
 unfold omega in |- *; auto with llists.
 intros; autorewrite with llists  using auto with llists.
 apply bisimilar_refl.
 intros; autorewrite with llists  using auto with llists.
Qed.

Lemma omega_lappend :
 forall (A:Type) (u:LList A), bisimilar (omega u) (LAppend u (omega u)).
Proof.
 intros; unfold omega at 1 in |- *; apply general_omega_lappend.
Qed.

Definition bisimulation (A:Type) (R:LList A -> LList A -> Prop) :=
  forall l1 l2:LList A,
     R l1 l2 ->
     match l1 with
     | LNil => l2 = LNil
     | LCons a l'1 =>
         match l2 with
         | LNil => False
         | LCons b l'2 => a = b /\ R l'1 l'2
         end
     end.
 
Theorem park_principle :
  forall (A:Type) (R:LList A -> LList A -> Prop),
    bisimulation R -> forall l1 l2:LList A, R l1 l2 -> bisimilar l1 l2. 
Proof.
 intros A R bisim; cofix H.
 intros l1 l2; case l1; case l2.
 left.
 intros a l H0.
 unfold bisimulation in bisim.
 generalize (bisim _ _ H0).
 intro H1; discriminate H1.
 intros a l H0.
 unfold bisimulation in bisim.
 generalize (bisim _ _ H0).
 simple induction 1.
 intros a l a0 l0 H0. 
 generalize (bisim _ _ H0).
(* intros.
 destruct H1.
 rewrite H1.
 constructor.
 apply H.
 assumption.
*)
 simple induction 1.
 simple induction 1.
 right.
 apply H.
 assumption.
Qed.

CoFixpoint alter  : LList bool := LCons true (LCons false alter).

Definition alter2 : LList bool := omega (LCons true (LCons false LNil)).

Definition R (l1 l2:LList bool) : Prop :=
  l1 = alter /\ l2 = alter2 \/
  l1 = LCons false alter /\ l2 = LCons false alter2.


Lemma R_bisim : bisimulation R.
Proof.
 unfold R, bisimulation in |- *.
 repeat simple induction 1.
 rewrite H1; rewrite H2; simpl in |- *.
 split; auto.
 right; split; auto.
 rewrite general_omega_LCons. 
 unfold alter2, omega in |- *; trivial.
 rewrite general_omega_shoots_again; trivial.
 rewrite H1; rewrite H2; simpl in |- *.
 split; auto.
Qed.

Lemma R_useful : R alter alter2.
Proof.
 left; auto.
Qed.

Lemma final : bisimilar alter alter2.
Proof. 
 apply park_principle with R.
 apply R_bisim.
 apply R_useful.
Qed.



(* LTL operators *)
 
Section LTL.
Variables (A : Type) (a b c : A).


Definition satisfies (l:LList A) (P:LList A -> Prop) : Prop := P l.
Hint Unfold satisfies: llists.

 Inductive Atomic (At:A -> Prop) : LList A -> Prop :=
     Atomic_intro : forall (a:A) (l:LList A), At a -> Atomic At (LCons a l).

 Hint Resolve Atomic_intro: llists.

 Inductive Next (P:LList A -> Prop) : LList A -> Prop :=
     Next_intro : forall (a:A) (l:LList A), P l -> Next P (LCons a l).

 Hint Resolve Next_intro: llists.

 Lemma Next_example : satisfies (LCons a (forever b)) (Next (Atomic (eq b))).
 Proof.
   rewrite (forever_unfold b); auto with llists. 
 Qed.


   
  
 Inductive Eventually (P:LList A -> Prop) : LList A -> Prop :=
   | Eventually_here :
       forall (a:A) (l:LList A), P (LCons a l) -> Eventually P (LCons a l)
   | Eventually_further :
       forall (a:A) (l:LList A), Eventually P l -> Eventually P (LCons a l).

 Hint Resolve Eventually_here Eventually_further: llists.


 Lemma Eventually_of_LAppend :
  forall (P:LList A -> Prop) (u v:LList A),
    Finite u ->
    satisfies v (Eventually P) -> satisfies (LAppend u v) (Eventually P).
 Proof.                       
  unfold satisfies in |- *; simple induction 1; intros;
   autorewrite with llists  using auto with llists.
 Qed.

 CoInductive Always (P:LList A -> Prop) : LList A -> Prop :=
    Always_LCons :
        forall (a:A) (l:LList A),
          P (LCons a l) -> Always P l -> Always P (LCons a l).

  
 Hint Resolve Always_LCons: llists.

 Lemma Always_Infinite :
   forall (P:LList A -> Prop) (l:LList A),
     satisfies l (Always P) -> Infinite l.
 Proof.
  intro P; cofix H.
  simple destruct l. 
  intro H0; inversion H0.
  intros a0 l0 H0; split.
  apply H; auto.
  inversion H0; auto.
 Qed.


 Definition F_Infinite (P:LList A -> Prop) : LList A -> Prop :=
   Always (Eventually P).

  Definition F_Infinite_2_Eventually : forall P l, F_Infinite P l-> Eventually P l.
 intros P l. 
  case l.
  inversion 1.
  inversion 1.
   assumption.
 Defined.

Section A_Proof_with_F_Infinite.
   
   Let w : LList A := LCons a (LCons b LNil).

   Let w_omega := omega w.

   Let P (l:LList A) : Prop := l = w_omega \/ l = LCons b w_omega.


  Remark P_F_Infinite :
   forall l:LList A, P l -> satisfies l (F_Infinite (Atomic (eq a))).
  Proof.
   unfold F_Infinite in |- *.
   cofix P_F_Infinite.
   intro l; simple destruct 1.
   intro eg; rewrite eg.
   unfold w_omega in |- *; rewrite omega_of_Finite.
   unfold w in |- *.
   autorewrite with llists  using auto with llists.
   split.
   auto with llists.
   apply P_F_Infinite.
   unfold P in |- *; auto.
   unfold w in |- *; auto with llists.
   intro eg; rewrite eg.
   unfold w_omega in |- *; rewrite omega_of_Finite.
   unfold w in |- *.
   rewrite LAppend_LCons.
   split.
   auto with llists.
   apply P_F_Infinite.
   unfold P in |- *; left.
   rewrite <- LAppend_LCons.
   rewrite <- omega_of_Finite.
   trivial.
   auto with llists.
   unfold w in |- *; auto with llists.
  Qed.

  Lemma omega_F_Infinite : satisfies w_omega (F_Infinite (Atomic (eq a))).
  Proof.
   apply P_F_Infinite.
   unfold P in |- *; left.
   trivial.
  Qed.

 End A_Proof_with_F_Infinite.

 Theorem F_Infinite_cons :
  forall (P:LList A -> Prop) (a:A) (l:LList A),
    satisfies l (F_Infinite P) -> satisfies (LCons a l) (F_Infinite P).
 Proof.
  split.
  inversion H.
  right.
  auto.
  assumption.
 Qed.

 Theorem F_Infinite_consR :
 forall (P:LList A -> Prop) (a:A) (l:LList A),
   satisfies (LCons a l) (F_Infinite P) -> satisfies l (F_Infinite P).
 Proof.
  inversion 1.
  assumption.
 Qed.

 Definition G_Infinite (P:LList A -> Prop) : LList A -> Prop :=
   Eventually (Always P).

 Lemma always_a : satisfies (forever a) (Always (Atomic (eq a))).
 Proof.
  unfold satisfies in |- *; cofix H.
  rewrite (forever_unfold a).
  auto with llists.
 Qed.

 Lemma LAppend_G_Infinite :
  forall (u v:LList A) (P:LList A -> Prop),
    Finite u ->
    satisfies v (G_Infinite P) -> 
    satisfies (LAppend u v) (G_Infinite P).
 Proof.
  simple induction 1.
  autorewrite with llists  using auto.
  intros; autorewrite with llists  using auto.
  unfold G_Infinite in |- *; auto with llists.
  right.
  apply H1.
  auto.
 Qed.

 Lemma LAppend_G_Infinite_R :
  forall (u v:LList A) (P:LList A -> Prop),
    Finite u ->
    satisfies (LAppend u v) (G_Infinite P) -> 
    satisfies v (G_Infinite P).
 Proof.
  simple induction 1.
  autorewrite with llists  using auto.
  intros; autorewrite with llists using auto.
  rewrite LAppend_LCons in H2.
  inversion_clear H2.
  apply H1.
  inversion_clear H3.
  generalize H4; case (LAppend l v).
  intro H5; inversion H5.  
  left.
  auto.
  auto.
 Qed.

End LTL.

Hint Unfold satisfies: llists.
Hint Resolve Always_LCons: llists.
Hint Resolve Eventually_here Eventually_further: llists.
Hint Resolve Next_intro: llists.
Hint Resolve Atomic_intro: llists.

(* Automata *)

Record automaton : Type := mk_auto
  {states : Set;
   actions : Set;
   initial : states;
   transitions : states -> actions -> list states}.

Hint Unfold transitions: automata.

Definition deadlock (A:automaton) (q:states A) :=
  forall a:actions A, @transitions A q a = nil.



Unset Implicit Arguments.
Set Strict Implicit.
CoInductive Trace (A:automaton) : states A -> LList (actions A) -> Prop :=
  | empty_trace : forall q:states A, deadlock A q -> Trace A q LNil 
  | lcons_trace :
      forall (q q':states A) (a:actions A) (l:LList (actions A)),
        In q' (transitions A q a) -> Trace A q' l -> Trace A q (LCons a l).
Set Implicit Arguments.
Unset Strict Implicit.


Section exemple.

(* states *)
Inductive st : Set :=
  | q0 : st
  | q1 : st
  | q2 : st.

(* actions *)
Inductive acts : Set :=
  | a : acts
  | b : acts.


(* transitions *)
Definition trans (q:st) (x:acts) : list st :=
  match q, x with
  | q0, a => q1 :: nil
  | q0, b => q1 :: nil
  | q1, a => q2 :: nil
  | q2, b => q2 :: q1 :: nil
  | _, _ => nil
  end.

(* a toy automaton *)
Definition A1 := mk_auto q0 trans.
      
Hint Unfold A1.

Lemma no_deadlocks : forall q:states A1, ~ deadlock  A1 q.
Proof.
 unfold deadlock in |- *; simple destruct q; intro H.
 absurd (transitions A1 q0 a = nil). 
 simpl in |- *; discriminate.
 auto.
 absurd (transitions A1 q1 a = nil). 
 simpl in |- *; discriminate.
 auto.
 absurd (transitions A1 q2 b = nil). 
 simpl in |- *; discriminate.
 auto.
Qed.

Lemma from_q1 :
 forall t:LList acts,
   Trace A1 q1 t ->
    exists t' : LList acts, Trace A1 q2 t' /\ t = LCons a t'.
Proof.
 intros t H; inversion_clear H.
 case (no_deadlocks H0). 
 generalize H0 H1; case a0; simpl in |- *.
 do 2 simple destruct 1.
 exists l; auto.
 contradiction. 
Qed.



Lemma from_q0 :
 forall t:LList acts,
   Trace A1 q0 t ->
    exists t' : LList acts,
     Trace A1 q2 t' /\ (t = LCons a (LCons a t') \/ t = LCons b (LCons a t')).
Proof.
 intros t H; inversion_clear H.
 case (no_deadlocks H0). 
 generalize H0 H1; case a0; simpl in |- *.
 do 2 simple destruct 1.
 intro H3; case (from_q1 H3).
 intros x [H4 H5].
 exists x; auto.
 rewrite H5; auto.
 do 2 simple destruct 1.
 intro H3; case (from_q1 H3).
 intros x [H4 H5].
 exists x; auto.
 rewrite H5; auto.
Qed.

Lemma from_q2 :
 forall t:LList acts,
   Trace A1 q2 t ->
    exists t' : LList acts,
     (Trace A1 q2 t' \/ Trace A1 q1 t') /\ t = LCons b t'.
Proof.
 intros t H; inversion_clear H.
 case (no_deadlocks H0).  
 generalize H0 H1; case a0; simpl in |- *.
 contradiction.
 do 2 simple destruct 1.
 exists l; auto.
 exists l; auto.
 rewrite H3; auto.
 contradiction.
Qed.

Theorem Infinite_bs :
 forall (q:states A1) (t:LList acts),
   Trace A1 q t -> satisfies t (F_Infinite (Atomic (eq b))).
Proof.
 cofix Infinite_bs.
 intros q; case q.
 intros t Ht; case (from_q0 Ht). 
 intros x [tx [ea| eb]].
 rewrite ea; split.
 case (from_q2 tx).
 intros x0 [[t2| t1] e]; rewrite e; auto with llists.
 split.
 case (from_q2 tx).
 intros x0 [_ e]; rewrite e; auto with llists.
 apply Infinite_bs with q2; auto.
 rewrite eb; split.  
 auto with llists.
 case (from_q2 tx).
 intros x0 [_ e]; rewrite e.
 split.
 auto with llists. 
 case e; apply Infinite_bs with q2; auto.
 intros t Ht; case (from_q1 Ht).
 intros x [tx e]; rewrite e.
 split.
 case (from_q2 tx).
 intros x0 [_ e']; rewrite e'; auto with llists.
 apply Infinite_bs with q2; auto.
 intros t Ht; case (from_q2 Ht).
 intros x [[t1| t2] e]; rewrite e.  
 split.
 auto with llists.
 apply Infinite_bs with q2; auto.
 split.
 auto with llists.
 apply Infinite_bs with q1; auto.
Qed.

End exemple.

