Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : int, forall y1 : int, (((~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 y1)) -> (rem y0 y1) = y0.
