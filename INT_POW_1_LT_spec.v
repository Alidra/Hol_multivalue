Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307722 : forall n : nat, forall x : int, ((~ (n = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) x) /\ (int_lt x (int_of_num (NUMERAL (BIT1 0)))))) -> int_lt (int_pow x n) (int_of_num (NUMERAL (BIT1 0))).
