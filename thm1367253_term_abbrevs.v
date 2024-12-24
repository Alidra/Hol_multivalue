Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := ((real_mul (real_of_num (NUMERAL 0)) (real_neg (real_of_num x0))) = (real_of_num (NUMERAL 0))) /\ (((real_mul (real_of_num x0) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
