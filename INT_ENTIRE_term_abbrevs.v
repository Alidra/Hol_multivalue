Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 := real_of_int (int_of_num (NUMERAL 0)).
Definition term4 := real_of_num (NUMERAL 0).
Definition term11 := int_of_num (NUMERAL 0).
Definition term3 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term7 (x0 : int) (x1 : int) := @eq real (real_mul (real_of_int x0) (real_of_int x1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => ((real_mul (real_of_int x0) y0) = (real_of_num (NUMERAL 0))) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0))))) (real_of_int x1).
Definition term17 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term9 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = (real_of_num (NUMERAL 0))))) (real_of_int x0).
Definition term1 (x0 : int) := forall y0 : real, ((real_mul (real_of_int x0) y0) = (real_of_num (NUMERAL 0))) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term18 (x0 : int) := forall y0 : int, ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) = ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_of_num (NUMERAL 0)))).
Definition term5 (x0 : int) (x1 : int) := ((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ ((real_of_int x1) = (real_of_num (NUMERAL 0))).
Definition term19 := forall y0 : int, forall y1 : int, ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ (y1 = (int_of_num (NUMERAL 0)))).
Definition term8 (x0 : int) (x1 : int) := @eq real (real_of_int (int_mul x0 x1)).
Definition term13 (x0 : int) (x1 : int) := @eq Prop ((int_mul x0 x1) = (int_of_num (NUMERAL 0))).
Definition term12 (x0 : int) (x1 : int) := @eq Prop ((real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num (NUMERAL 0))).
Definition term15 (x0 : int) := or ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term6 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term14 (x0 : int) := @eq real (real_of_int x0).
Definition term16 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).