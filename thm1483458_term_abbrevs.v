Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := real_of_num (NUMERAL 0).
Definition term0 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).