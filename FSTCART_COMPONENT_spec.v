Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7664619 : forall {A M N : Type'}, forall x : cart A (finite_sum M N), forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex M (@UNIV M)))) -> (@dollar A M (@fstcart A M N x) i) = (@dollar A (finite_sum M N) x i).
