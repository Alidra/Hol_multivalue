Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : int) := real_sgn (real_of_int x0).
Definition term2 := real_of_int (int_of_num (NUMERAL 0)).
Definition term1 := real_of_num (NUMERAL 0).
Definition term8 := int_of_num (NUMERAL 0).
Definition term3 := real_sgn (real_of_num (NUMERAL 0)).
Definition term0 (x0 : nat) := real_of_int (int_of_num x0).
Definition term4 := real_sgn (real_of_int (int_of_num (NUMERAL 0))).
Definition term6 (x0 : int) := real_of_int (int_sgn x0).
Definition term7 := real_of_int (int_sgn (int_of_num (NUMERAL 0))).
Definition term11 := int_sgn (int_of_num (NUMERAL 0)).
Definition term9 := @eq real (real_sgn (real_of_num (NUMERAL 0))).
Definition term10 := @eq real (real_of_int (int_sgn (int_of_num (NUMERAL 0)))).