Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 := real_of_int (int_of_num (NUMERAL 0)).
Definition term13 := real_of_num (NUMERAL 0).
Definition term16 := int_of_num (NUMERAL 0).
Definition term5 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term19 (x0 : int) (x1 : int) (x2 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (x1 = x2).
Definition term8 (x0 : int) (x1 : int) := @eq real (real_mul (real_of_int x0) (real_of_int x1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, ((real_mul (real_of_int x0) y0) = (real_mul (real_of_int x0) y1)) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ (y0 = y1))) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, ((real_mul (real_of_int x0) y0) = (real_mul (real_of_int x0) y1)) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ (y0 = y1)).
Definition term20 (x0 : int) (x1 : int) := forall y0 : int, ((int_mul x0 x1) = (int_mul x0 y0)) = ((x0 = (int_of_num (NUMERAL 0))) \/ (x1 = y0)).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, ((real_mul (real_of_int x0) (real_of_int x1)) = (real_mul (real_of_int x0) y0)) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ ((real_of_int x1) = y0)).
Definition term12 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_mul y0 y1) = (real_mul y0 y2)) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = y2))) (real_of_int x0).
Definition term10 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((real_mul (real_of_int x1) (real_of_int x0)) = (real_mul (real_of_int x1) (real_of_int x2))).
Definition term22 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_mul y0 y1) = (int_mul y0 y2)) = ((y0 = (int_of_num (NUMERAL 0))) \/ (y1 = y2)).
Definition term21 (x0 : int) := forall y0 : int, forall y1 : int, ((int_mul x0 y0) = (int_mul x0 y1)) = ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = y1)).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => ((real_mul (real_of_int x0) (real_of_int x1)) = (real_mul (real_of_int x0) y0)) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ ((real_of_int x1) = y0))) (real_of_int x2).
Definition term9 (x0 : int) (x1 : int) := @eq real (real_of_int (int_mul x0 x1)).
Definition term11 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((int_mul x1 x0) = (int_mul x1 x2)).
Definition term17 (x0 : int) := or ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term7 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term15 (x0 : int) := @eq real (real_of_int x0).
Definition term18 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := ((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ ((real_of_int x1) = (real_of_int x2)).
