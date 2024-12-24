Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309136 : forall x : int, forall y : int, ((int_sgn x) = (int_sgn y)) = (((x = (int_of_num (NUMERAL 0))) = (y = (int_of_num (NUMERAL 0)))) /\ (((int_gt x (int_of_num (NUMERAL 0))) = (int_gt y (int_of_num (NUMERAL 0)))) /\ ((int_lt x (int_of_num (NUMERAL 0))) = (int_lt y (int_of_num (NUMERAL 0)))))).
