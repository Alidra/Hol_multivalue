Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308605 : forall n : nat, forall x : int, forall y : int, ((int_le (int_of_num (NUMERAL 0)) y) /\ (int_lt (int_pow x n) (int_pow y n))) -> int_lt x y.