Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1863601 : forall x : real, forall y : real, ((real_sgn x) = (real_sgn y)) = (((x = (real_of_num (NUMERAL 0))) -> y = (real_of_num (NUMERAL 0))) /\ (((real_gt x (real_of_num (NUMERAL 0))) -> real_gt y (real_of_num (NUMERAL 0))) /\ ((real_lt x (real_of_num (NUMERAL 0))) -> real_lt y (real_of_num (NUMERAL 0))))).
