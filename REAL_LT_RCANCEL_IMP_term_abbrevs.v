Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term30 := fun y0 : real => True.
Definition term7 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term21 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 x0) (real_mul y0 x1))) -> real_lt x0 x1.
Definition term20 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul x0 y0) (real_mul x1 y0))) -> real_lt x0 x1.
Definition term31 := forall y0 : real, True.
Definition term33 (x0 : Prop) := forall y0 : real, x0.
Definition term29 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y2 y0) (real_mul y2 y1))) -> real_lt y0 y1.
Definition term28 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1.
Definition term25 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul y1 x0) (real_mul y1 y0))) -> real_lt x0 y0.
Definition term24 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul x0 y1) (real_mul y0 y1))) -> real_lt x0 y0.
Definition term1 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 y0) (real_mul x0 y1))) -> real_lt y0 y1.
Definition term15 (x0 : real) (x1 : real) (x2 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_mul x0 x2) (real_mul x1 x2))).
Definition term13 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_mul x0 x2) (real_mul x1 x2)).
Definition term12 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term9 (x0 : real) (x1 : real) := real_lt (real_mul x0 x1).
Definition term16 (x0 : real) (x1 : real) (x2 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_mul x1 x0) (real_mul x1 x2))).
Definition term23 (x0 : real) := fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul y1 x0) (real_mul y1 y0))) -> real_lt x0 y0.
Definition term22 (x0 : real) := fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul x0 y1) (real_mul y0 y1))) -> real_lt x0 y0.
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term17 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x1 x0) (real_mul x2 x0))) -> real_lt x1 x2.
Definition term5 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 x2))) -> real_lt x1 x2.
Definition term19 (x0 : real) (x1 : real) := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 x0) (real_mul y0 x1))) -> real_lt x0 x1.
Definition term18 (x0 : real) (x1 : real) := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul x0 y0) (real_mul x1 y0))) -> real_lt x0 x1.
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 y0) (real_mul x0 y1))) -> real_lt y0 y1) x1.
Definition term10 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_mul x0 x2) (real_mul x1 x2).
Definition term27 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y2 y0) (real_mul y2 y1))) -> real_lt y0 y1.
Definition term26 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1.
Definition term3 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 y0))) -> real_lt x1 y0.
Definition term14 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_mul x1 x0) (real_mul x1 x2)).
Definition term11 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_mul x1 x0) (real_mul x1 x2).
Definition term4 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 y0))) -> real_lt x1 y0) x2.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 y1) (real_mul y0 y2))) -> real_lt y1 y2) x0.
