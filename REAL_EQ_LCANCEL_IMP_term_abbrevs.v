Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term14 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y0) = (real_mul x1 y0))) -> x0 = x1.
Definition term13 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 x0) = (real_mul y0 x1))) -> x0 = x1.
Definition term8 (x0 : real) (x1 : real) (x2 : real) := imp ((~ (x2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 x2) = (real_mul x1 x2))).
Definition term7 (x0 : real) (x1 : real) (x2 : real) := imp ((~ (x1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x1 x0) = (real_mul x1 x2))).
Definition term22 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 y2) = (real_mul y1 y2))) -> y0 = y1.
Definition term21 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1.
Definition term18 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y1) = (real_mul y0 y1))) -> x0 = y0.
Definition term17 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y1 x0) = (real_mul y1 y0))) -> x0 = y0.
Definition term12 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y0) = (real_mul x1 y0))) -> x0 = x1.
Definition term11 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 x0) = (real_mul y0 x1))) -> x0 = x1.
Definition term16 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y1) = (real_mul y0 y1))) -> x0 = y0.
Definition term15 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y1 x0) = (real_mul y1 y0))) -> x0 = y0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y1) = (real_mul y0 y1))) -> x0 = y0) x1.
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x1 x0) = (real_mul x1 x2)).
Definition term20 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 y2) = (real_mul y1 y2))) -> y0 = y1.
Definition term19 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1.
Definition term3 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x1 x0) = (real_mul x2 x0))) -> x1 = x2.
Definition term9 (x0 : real) (x1 : real) (x2 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 x1) = (real_mul x0 x2))) -> x1 = x2.
Definition term4 (x0 : real) := and (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term23 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 y2) = (real_mul y1 y2))) -> y0 = y1) x0.
Definition term25 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y0) = (real_mul x1 y0))) -> x0 = x1) x2.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 x2) = (real_mul x1 x2)).
