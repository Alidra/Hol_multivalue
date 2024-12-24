Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term10 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term7 := real_of_int (int_of_num (NUMERAL 0)).
Definition term6 := real_of_num (NUMERAL 0).
Definition term14 := int_of_num (NUMERAL 0).
Definition term8 := real_lt (real_of_num (NUMERAL 0)).
Definition term5 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_lt y1 y0)) (real_of_int x0).
Definition term3 (x0 : int) (x1 : int) := real_lt (real_of_num (NUMERAL 0)) (real_sub (real_of_int x0) (real_of_int x1)).
Definition term4 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_sub (real_of_int x0) y0)) = (real_lt y0 (real_of_int x0))) (real_of_int x1).
Definition term16 (x0 : int) (x1 : int) := @eq Prop (int_lt (int_of_num (NUMERAL 0)) (int_sub x0 x1)).
Definition term15 (x0 : int) (x1 : int) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (real_sub (real_of_int x0) (real_of_int x1))).
Definition term18 := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) (int_sub y0 y1)) = (int_lt y1 y0).
Definition term13 (x0 : int) (x1 : int) := int_lt (int_of_num (NUMERAL 0)) (int_sub x0 x1).
Definition term9 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub (real_of_int x0) y0)) = (real_lt y0 (real_of_int x0)).
Definition term12 (x0 : int) (x1 : int) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_sub x0 x1)).
Definition term17 (x0 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) (int_sub x0 y0)) = (int_lt y0 x0).
