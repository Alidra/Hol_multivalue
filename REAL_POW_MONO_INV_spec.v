Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1649379 : forall m : nat, forall n : nat, forall x : real, ((real_le (real_of_num (NUMERAL 0)) x) /\ ((real_le x (real_of_num (NUMERAL (BIT1 0)))) /\ (Peano.le n m))) -> real_le (real_pow x m) (real_pow x n).
