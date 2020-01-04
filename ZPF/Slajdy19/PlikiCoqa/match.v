Inductive I : bool -> Type :=
|A : I true
|B : I false
|C' : I true
.

Definition w (b:bool)(x:I b): I b :=  
match x as y in I c return I c with 
| A => A (* neither x nor y does not fit here*) 
| B => B
| C' => C' (* A fits here *)
end.

Arguments w [b] _.

Eval simpl in (w A).
Eval simpl in (w B).


Inductive J : bool -> Type :=
|Aj : J true
|Bj : J false
|C : forall (b:bool), J b -> J b.

Definition wj (b:bool)(x:J b): J b :=  
match x as y in J b' return J b' with 
| Aj => Aj
| Bj => Bj
| C _ z => z
end.

Arguments wj [b] _.
Arguments C [b] _.

Eval simpl in (wj Aj).
Eval simpl in (wj (C Bj)).

