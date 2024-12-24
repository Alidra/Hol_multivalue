Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7670352 : forall {A M N : Type'}, (forall u : cart A M, forall v : cart A N, forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex M (@UNIV M)))) -> (@dollar A (finite_sum M N) (@pastecart A M N u v) i) = (@dollar A M u i)) /\ (forall u : cart A M, forall v : cart A N, forall i : nat, ((Peano.le (Nat.add (@dimindex M (@UNIV M)) (NUMERAL (BIT1 0))) i) /\ (Peano.le i (Nat.add (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))))) -> (@dollar A (finite_sum M N) (@pastecart A M N u v) i) = (@dollar A N v (Nat.sub i (@dimindex M (@UNIV M))))).
