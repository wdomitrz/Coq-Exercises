Set Implicit Arguments.

Section ilist.
Variable A : Set.

Inductive ilist : nat -> Set :=
| Nil : ilist 0
| Cons : forall n, A -> ilist n -> ilist (S n).

Print ilist.

Fixpoint app' n1 (l1:ilist n1) n2 (l2:ilist n2): ilist (n1+n2) :=
match l1 in (ilist k) return ilist(k+n2) with
| Nil => l2
| Cons x ls' => Cons x (app' ls' l2)
end. 


Print ilist.
(*
End ilist.

Print ilist.
*)


Definition hd n (ls : ilist (S n)) : A :=
match ls with
| Cons h _ => h
end.

Print hd.

(*hd = 
fun (n : nat) (ls : ilist (S n)) =>
match
  ls as ls0 in (ilist n0)
  return
    (match n0 as x return (ilist x -> Type) with
     | 0 => fun _ : ilist 0 => ID
     | S n1 => fun _ : ilist (S n1) => A
     end ls0)
with
| Nil => id
| Cons _ h _ => h
end
     : forall n : nat, ilist (S n) -> A
*)

Definition hd1 := fun (n : nat) (ls : ilist (S n)) =>
match ls as ls0 in (ilist n0)
  return (match n0 with
         | 0 => unit
         | S n1 => A
         end)
with
| Nil => tt
| Cons h _ => h
end.

Print hd1.
Check hd1.

Variable a:A.


Eval simpl in (hd1 (Cons a Nil)). 



Definition hd_pom n (ls : ilist n) :=
match ls in (ilist n) return 
      (match n with O => unit | S _ => A end) with
| Nil => tt
| Cons h _ => h
end.

Check hd_pom.

Definition hd2 n (ls : ilist (S n)) : A 
   := hd_pom ls.

Print hd2.
Check hd2.

Eval simpl in (hd2 (Cons a Nil)). 


Definition hd3 := fun (n : nat) (ls : ilist (S n)) =>
match
  ls as ls0 in (ilist n0)
  return
    (match n0 as x return (ilist x -> Type) with
     | 0 => fun _ : ilist 0 => unit
     | S n1 => fun _ : ilist (S n1) => A
     end ls0)
with
| Nil => tt
| Cons h _ => h
end.

Print hd3.
Check hd3.

Eval simpl in (hd3 (Cons a Nil)). 


End ilist.





