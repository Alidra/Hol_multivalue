Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term8 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x0 y0)) -> real_lt (real_mul x1 x0) (real_mul x1 y0)) x2.
Definition term30 (x0 : real) (x1 : real) := real_mul (real_mul (real_inv x0) x0) x1.
Definition term38 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_mul (real_inv x0) (real_mul x0 x1)) (real_mul (real_inv x0) (real_mul x0 x2))) -> real_lt x1 x2.
Definition term16 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x1)) /\ (real_lt (real_mul x1 x0) (real_mul x1 x2)).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_mul (real_inv x1) (real_mul x1 x0)) (real_mul (real_inv x1) (real_mul x1 x2)).
Definition term44 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 y1) (real_mul y0 y2))) -> real_lt y1 y2.
Definition term43 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 y0) (real_mul x0 y1))) -> real_lt y0 y1.
Definition term23 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term5 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt y0 y1)) -> real_lt (real_mul x0 y0) (real_mul x0 y1).
Definition term2 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term40 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) /\ (real_lt (real_mul x0 x1) (real_mul x0 x2))) -> real_lt x1 x2.
Definition term39 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_lt x0 x1.
Definition term26 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term1 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term7 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x0 y0)) -> real_lt (real_mul x1 x0) (real_mul x1 y0).
Definition term3 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term19 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term20 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term11 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term25 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term29 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_mul x0 x1).
Definition term36 (x0 : real) (x1 : real) (x2 : real) := imp (real_lt (real_mul (real_inv x1) (real_mul x1 x0)) (real_mul (real_inv x1) (real_mul x1 x2))).
Definition term21 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term9 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x0 x2)) -> real_lt (real_mul x1 x0) (real_mul x1 x2).
Definition term37 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 x2))) -> real_lt x1 x2.
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term6 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt y0 y1)) -> real_lt (real_mul x0 y0) (real_mul x0 y1)) x1.
Definition term10 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) x0.
Definition term34 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term13 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term33 (x0 : real) := real_mul (real_mul (real_inv x0) x0).
Definition term32 := real_of_num (NUMERAL (BIT1 0)).
Definition term42 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 y0))) -> real_lt x1 y0.
Definition term28 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term12 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_mul x1 x0) (real_mul x1 x2)).
Definition term14 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_mul x1 x0) (real_mul x1 x2).
Definition term15 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term31 (x0 : real) := real_mul (real_inv x0) x0.
Definition term35 (x0 : real) (x1 : real) := real_lt (real_mul (real_inv x0) (real_mul x0 x1)).
Definition term17 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv x1)) /\ (real_lt (real_mul x1 x0) (real_mul x1 x2))) -> real_lt (real_mul (real_inv x1) (real_mul x1 x0)) (real_mul (real_inv x1) (real_mul x1 x2)).
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y1 y2)) -> real_lt (real_mul y0 y1) (real_mul y0 y2)) x0.
