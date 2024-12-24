Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, forall y4 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((int_add y1 (int_mul y0 y3)) = (int_add y2 (int_mul y0 y4))).
