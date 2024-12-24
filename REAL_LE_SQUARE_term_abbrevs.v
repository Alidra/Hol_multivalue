Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term1 (x0 : real) := real_neg (real_neg x0).
Definition term28 (x0 : real) := real_mul x0 (real_neg x0).
Definition term12 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term22 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term34 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x0))) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term14 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term5 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term26 (x0 : real) := real_mul (real_neg x0) (real_neg x0).
Definition term23 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_neg x0))) -> real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x0)).
Definition term31 := real_le (real_of_num (NUMERAL 0)).
Definition term17 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term6 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term33 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)).
Definition term21 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term18 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term24 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term3 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term30 (x0 : real) := real_neg (real_neg (real_mul x0 x0)).
Definition term10 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term13 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term27 (x0 : real) := real_neg (real_mul x0 (real_neg x0)).
Definition term8 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term29 (x0 : real) := real_neg (real_mul x0 x0).
Definition term20 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term11 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg y0))) x0.
Definition term32 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x0))).
Definition term19 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term15 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term25 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term35 := forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0).
