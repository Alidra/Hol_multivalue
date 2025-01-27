Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) := ((~ (x0 = x1)) = ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0))) /\ ((int_lt x0 x1) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
