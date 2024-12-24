Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : int) (x1 : int) (x2 : int) := imp ((~ ((real_of_int x2) = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_int x0) (real_of_int x2)) = (real_mul (real_of_int x1) (real_of_int x2)))).
Definition term8 := real_of_int (int_of_num (NUMERAL 0)).
Definition term7 := real_of_num (NUMERAL 0).
Definition term10 := int_of_num (NUMERAL 0).
Definition term15 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_int x0) y0) = (real_mul (real_of_int x1) y0))) -> (real_of_int x0) = (real_of_int x1)) (real_of_int x2).
Definition term17 (x0 : int) (x1 : int) := @eq real (real_mul (real_of_int x0) (real_of_int x1)).
Definition term11 (x0 : int) := ~ ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term22 (x0 : int) (x1 : int) (x2 : int) := imp ((~ (x2 = (int_of_num (NUMERAL 0)))) /\ ((int_mul x0 x2) = (int_mul x1 x2))).
Definition term24 (x0 : int) (x1 : int) := forall y0 : int, ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ ((int_mul x0 y0) = (int_mul x1 y0))) -> x0 = x1.
Definition term19 (x0 : int) (x1 : int) (x2 : int) := (~ ((real_of_int x2) = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_int x0) (real_of_int x2)) = (real_mul (real_of_int x1) (real_of_int x2))).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_int x0) y1) = (real_mul y0 y1))) -> (real_of_int x0) = y0) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_int x0) y1) = (real_mul y0 y1))) -> (real_of_int x0) = y0.
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := ((~ ((real_of_int x0) = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_int x1) (real_of_int x0)) = (real_mul (real_of_int x2) (real_of_int x0)))) -> (real_of_int x1) = (real_of_int x2).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 y2) = (real_mul y1 y2))) -> y0 = y1) (real_of_int x0).
Definition term20 (x0 : int) (x1 : int) (x2 : int) := (~ (x2 = (int_of_num (NUMERAL 0)))) /\ ((int_mul x0 x2) = (int_mul x1 x2)).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_int x0) y0) = (real_mul (real_of_int x1) y0))) -> (real_of_int x0) = (real_of_int x1).
Definition term23 (x0 : int) (x1 : int) (x2 : int) := ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((int_mul x1 x0) = (int_mul x2 x0))) -> x1 = x2.
Definition term13 (x0 : int) := and (~ ((real_of_int x0) = (real_of_num (NUMERAL 0)))).
Definition term26 := forall y0 : int, forall y1 : int, forall y2 : int, ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ ((int_mul y0 y2) = (int_mul y1 y2))) -> y0 = y1.
Definition term25 (x0 : int) := forall y0 : int, forall y1 : int, ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ ((int_mul x0 y1) = (int_mul y0 y1))) -> x0 = y0.
Definition term12 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term18 (x0 : int) (x1 : int) := @eq real (real_of_int (int_mul x0 x1)).
Definition term16 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term9 (x0 : int) := @eq real (real_of_int x0).
Definition term14 (x0 : int) := and (~ (x0 = (int_of_num (NUMERAL 0)))).
