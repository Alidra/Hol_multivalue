Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318497 : forall (x : int) (y : int), ((~ (x = y)) = ((int_le (int_add x (int_of_num (NUMERAL (BIT1 0)))) y) \/ (int_le (int_add y (int_of_num (NUMERAL (BIT1 0)))) x))) /\ ((int_lt x y) = (int_le (int_add x (int_of_num (NUMERAL (BIT1 0)))) y)).
