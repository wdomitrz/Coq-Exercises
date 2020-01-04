module Parity



{- conversion

plus 3 4
\k => plus k 0
\k => plus Z k
\k,m => plus (S k) m
\k:Nat => 0+k
\k:Nat => k+0
\k => Z + k
 
-}





data Parity : Nat -> Type where
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))

{-
l1: Parity (S (plus j (S j))) -> Parity (S (S (plus j j)))
....
-}

parity : (n:Nat) -> Parity n
parity Z     = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | Even  = ?l1 (Even {n=S j})
    parity (S (S (S (j + j)))) | Odd  ?= (Odd {n=S j})


{-
---------- Proofs ----------
Parity.l1 = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc j j)
  trivial



Parity.parity_lemma_1 = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc j j)
  trivial
-}



{-

parity2 : (n:Nat) -> Parity n
parity2 Z     = Even {n = Z}
parity2 (S k) with (parity2 k)
    parity2 (S (j + j))     | Even ?= Odd {n=j}
    parity2 (S (S (j + j))) | Odd  ?= Even {n=S j}

-}
