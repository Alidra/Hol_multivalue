Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308379 : forall n : nat, forall x : int, forall y : int, ((~ (n = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) y) /\ (int_le (int_pow x n) (int_pow y n)))) -> int_le x y.
