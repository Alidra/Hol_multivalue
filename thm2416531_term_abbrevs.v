Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := int_of_num (NUMERAL 0).
Definition term0 (x0 : int) := int_mul (int_of_num (NUMERAL 0)) x0.
