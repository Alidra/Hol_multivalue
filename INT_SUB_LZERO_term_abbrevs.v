Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) := (fun y0 : real => (real_sub (real_of_num (NUMERAL 0)) y0) = (real_neg y0)) (real_of_int x0).
Definition term10 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term9 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term5 := real_of_int (int_of_num (NUMERAL 0)).
Definition term4 := real_of_num (NUMERAL 0).
Definition term12 := int_of_num (NUMERAL 0).
Definition term3 (x0 : nat) := real_of_int (int_of_num x0).
Definition term6 := real_sub (real_of_num (NUMERAL 0)).
Definition term1 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term11 (x0 : int) := real_of_int (int_sub (int_of_num (NUMERAL 0)) x0).
Definition term13 (x0 : int) := @eq real (real_sub (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term2 (x0 : int) := real_neg (real_of_int x0).
Definition term7 := real_sub (real_of_int (int_of_num (NUMERAL 0))).
Definition term16 (x0 : int) := int_sub (int_of_num (NUMERAL 0)) x0.
Definition term17 := forall y0 : int, (int_sub (int_of_num (NUMERAL 0)) y0) = (int_neg y0).
Definition term8 (x0 : int) := real_sub (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term15 (x0 : int) := real_of_int (int_neg x0).
Definition term14 (x0 : int) := @eq real (real_of_int (int_sub (int_of_num (NUMERAL 0)) x0)).