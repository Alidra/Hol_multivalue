Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : int) (x1 : int) := int_lt (int_add x0 x1) (int_of_num (NUMERAL 0)).
Definition term15 (x0 : int) (x1 : int) := real_lt (real_add (real_of_int x0) (real_of_int x1)).
Definition term19 := real_of_int (int_of_num (NUMERAL 0)).
Definition term18 := real_of_num (NUMERAL 0).
Definition term23 (x0 : int) := forall y0 : int, (int_lt x0 (int_neg y0)) = (int_lt (int_add x0 y0) (int_of_num (NUMERAL 0))).
Definition term22 := int_of_num (NUMERAL 0).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_lt (real_of_int x0) (real_neg y0)) = (real_lt (real_add (real_of_int x0) y0) (real_of_num (NUMERAL 0)))) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_neg (real_of_int x1)).
Definition term14 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term17 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_lt y0 (real_neg y1)) = (real_lt (real_add y0 y1) (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term13 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term9 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term12 (x0 : int) (x1 : int) := @eq Prop (int_lt x0 (int_neg x1)).
Definition term8 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int (int_neg x1)).
Definition term24 := forall y0 : int, forall y1 : int, (int_lt y0 (int_neg y1)) = (int_lt (int_add y0 y1) (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := forall y0 : real, (real_lt (real_of_int x0) (real_neg y0)) = (real_lt (real_add (real_of_int x0) y0) (real_of_num (NUMERAL 0))).
Definition term10 (x0 : int) (x1 : int) := int_lt x0 (int_neg x1).
Definition term5 (x0 : int) := real_neg (real_of_int x0).
Definition term11 (x0 : int) (x1 : int) := @eq Prop (real_lt (real_of_int x0) (real_neg (real_of_int x1))).
Definition term7 (x0 : int) := real_lt (real_of_int x0).
Definition term6 (x0 : int) := real_of_int (int_neg x0).
Definition term16 (x0 : int) (x1 : int) := real_lt (real_of_int (int_add x0 x1)).
Definition term4 (x0 : int) (x1 : int) := real_lt (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term20 (x0 : int) (x1 : int) := real_lt (real_of_int (int_add x0 x1)) (real_of_int (int_of_num (NUMERAL 0))).
