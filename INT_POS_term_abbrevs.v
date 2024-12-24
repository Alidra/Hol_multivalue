Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) x0.
Definition term4 := real_of_int (int_of_num (NUMERAL 0)).
Definition term3 := real_of_num (NUMERAL 0).
Definition term7 (x0 : nat) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num x0)).
Definition term10 := int_of_num (NUMERAL 0).
Definition term11 := forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0).
Definition term5 := real_le (real_of_num (NUMERAL 0)).
Definition term2 (x0 : nat) := real_of_int (int_of_num x0).
Definition term1 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term9 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term8 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term6 := real_le (real_of_int (int_of_num (NUMERAL 0))).
