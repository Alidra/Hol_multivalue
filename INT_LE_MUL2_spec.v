Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302816 : forall w : int, forall x : int, forall y : int, forall z : int, ((int_le (int_of_num (NUMERAL 0)) w) /\ ((int_le w x) /\ ((int_le (int_of_num (NUMERAL 0)) y) /\ (int_le y z)))) -> int_le (int_mul w y) (int_mul x z).
