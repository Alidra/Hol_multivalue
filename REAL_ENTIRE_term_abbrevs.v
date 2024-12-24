Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term2 := real_of_num (NUMERAL 0).
Definition term24 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term31 (x0 : real) (x1 : real) := imp ((real_mul (real_inv x1) (real_mul x1 x0)) = (real_mul (real_inv x1) (real_of_num (NUMERAL 0)))).
Definition term28 (x0 : real) (x1 : real) := real_mul (real_mul (real_inv x0) x0) x1.
Definition term13 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term50 := forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term6 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term35 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term9 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term36 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term15 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term44 (x0 : real) := imp (x0 = (real_of_num (NUMERAL 0))).
Definition term16 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term3 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term8 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term21 := @eq real (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term26 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_mul x0 x1).
Definition term49 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term4 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term45 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> x0 = (real_of_num (NUMERAL 0)).
Definition term43 (x0 : real) (x1 : real) := ((real_mul (real_of_num (NUMERAL (BIT1 0))) x1) = (real_mul (real_inv x0) (real_of_num (NUMERAL 0)))) -> x1 = (real_of_num (NUMERAL 0)).
Definition term34 (x0 : real) (x1 : real) := ((real_mul (real_mul (real_inv x0) x0) x1) = (real_mul (real_inv x0) (real_of_num (NUMERAL 0)))) -> x1 = (real_of_num (NUMERAL 0)).
Definition term17 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term14 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term19 := real_mul (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term48 (x0 : real) (x1 : real) := (((real_mul x0 x1) = (real_of_num (NUMERAL 0))) -> (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0)))) /\ (((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 x1) = (real_of_num (NUMERAL 0))).
Definition term40 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term42 (x0 : real) (x1 : real) := imp ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = (real_mul (real_inv x1) (real_of_num (NUMERAL 0)))).
Definition term32 (x0 : real) (x1 : real) := imp ((real_mul (real_mul (real_inv x1) x1) x0) = (real_mul (real_inv x1) (real_of_num (NUMERAL 0)))).
Definition term39 (x0 : real) := real_mul (real_mul (real_inv x0) x0).
Definition term29 (x0 : real) (x1 : real) := @eq real (real_mul (real_inv x0) (real_mul x0 x1)).
Definition term20 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term12 (x0 : real) := real_mul (real_inv x0).
Definition term38 := real_of_num (NUMERAL (BIT1 0)).
Definition term11 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term18 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term23 (x0 : real) := True \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term46 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 x1) = (real_of_num (NUMERAL 0)).
Definition term22 (x0 : real) := or (x0 = (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) (x1 : real) := @eq real (real_mul (real_mul (real_inv x0) x0) x1).
Definition term25 (x0 : real) := False \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term37 (x0 : real) := real_mul (real_inv x0) x0.
Definition term47 (x0 : real) (x1 : real) := ((real_mul x0 x1) = (real_of_num (NUMERAL 0))) -> (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term27 (x0 : real) := real_mul (real_inv x0) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term33 (x0 : real) (x1 : real) := ((real_mul (real_inv x0) (real_mul x0 x1)) = (real_mul (real_inv x0) (real_of_num (NUMERAL 0)))) -> x1 = (real_of_num (NUMERAL 0)).
