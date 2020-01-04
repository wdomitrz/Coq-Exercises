Check f_equal.
Check f_equal pred (eq_refl 0).

Lemma UIP_refl_nat (n:nat) (x : n = n) : x = eq_refl.
Proof.
  induction n.
  - change (match 0 as n return 0=n -> Prop with
            | 0 => fun x => x = eq_refl
            | _ => fun _ => True
            end x).
    destruct x; reflexivity.
  - specialize IHn with (f_equal pred x).
    change eq_refl with
           (match (@eq_refl _ n) in _ = n' return S n = S n' with
            | eq_refl => eq_refl
            end).
    rewrite <- IHn; clear IHn.
    change (match S n as n' return S n = n' -> Prop with
            | 0 => fun _ => True
            | S n' => fun x =>
                x = match f_equal pred x in _ = n' return S n = S n' with
                    | eq_refl => eq_refl
                    end
            end x).
  pattern (S n) at 2 3, x.
  destruct x. reflexivity.
Defined.
