Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318496 : forall (x : int) (y : int), ((~ (int_lt x y)) = (int_le y x)) /\ (((~ (x = y)) = ((int_le (int_add x (int_of_num (NUMERAL (BIT1 0)))) y) \/ (int_le (int_add y (int_of_num (NUMERAL (BIT1 0)))) x))) /\ ((int_lt x y) = (int_le (int_add x (int_of_num (NUMERAL (BIT1 0)))) y))).