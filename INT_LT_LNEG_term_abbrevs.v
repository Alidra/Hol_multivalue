Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 := real_of_int (int_of_num (NUMERAL 0)).
Definition term15 := real_of_num (NUMERAL 0).
Definition term23 := int_of_num (NUMERAL 0).
Definition term9 (x0 : int) (x1 : int) := real_lt (real_of_int (int_neg x0)) (real_of_int x1).
Definition term22 (x0 : int) (x1 : int) := int_lt (int_of_num (NUMERAL 0)) (int_add x0 x1).
Definition term20 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term17 := real_lt (real_of_num (NUMERAL 0)).
Definition term14 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_lt (real_neg y0) y1) = (real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) (real_of_int x0).
Definition term19 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term10 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term11 (x0 : int) (x1 : int) := int_lt (int_neg x0) x1.
Definition term21 (x0 : int) (x1 : int) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_add x0 x1)).
Definition term25 := forall y0 : int, forall y1 : int, (int_lt (int_neg y0) y1) = (int_lt (int_of_num (NUMERAL 0)) (int_add y0 y1)).
Definition term18 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term12 (x0 : int) (x1 : int) := @eq Prop (real_lt (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term5 (x0 : int) := real_neg (real_of_int x0).
Definition term4 (x0 : int) (x1 : int) := real_lt (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_int x1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_lt (real_neg (real_of_int x0)) y0) = (real_lt (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) y0))) (real_of_int x1).
Definition term8 (x0 : int) := real_lt (real_of_int (int_neg x0)).
Definition term6 (x0 : int) := real_of_int (int_neg x0).
Definition term1 (x0 : int) := forall y0 : real, (real_lt (real_neg (real_of_int x0)) y0) = (real_lt (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) y0)).
Definition term13 (x0 : int) (x1 : int) := @eq Prop (int_lt (int_neg x0) x1).
Definition term3 (x0 : int) (x1 : int) := real_lt (real_neg (real_of_int x0)) (real_of_int x1).
Definition term7 (x0 : int) := real_lt (real_neg (real_of_int x0)).
Definition term24 (x0 : int) := forall y0 : int, (int_lt (int_neg x0) y0) = (int_lt (int_of_num (NUMERAL 0)) (int_add x0 y0)).
