Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term38 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 x2) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 x3)))) -> int_lt (int_mul x0 x1) (int_mul x2 x3).
Definition term10 := real_of_int (int_of_num (NUMERAL 0)).
Definition term9 := real_of_num (NUMERAL 0).
Definition term17 := int_of_num (NUMERAL 0).
Definition term31 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term26 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 x3)).
Definition term39 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 x2) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 y0)))) -> int_lt (int_mul x0 x1) (int_mul x2 y0).
Definition term13 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)))) -> real_lt (real_mul (real_of_int x0) y1) (real_mul y0 y2)) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)))) -> real_lt (real_mul (real_of_int x0) y0) (real_mul (real_of_int x1) y1).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)))) -> real_lt (real_mul (real_of_int x0) y1) (real_mul y0 y2).
Definition term25 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (real_lt (real_of_int x0) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ (real_lt (real_of_int x2) (real_of_int x3))).
Definition term6 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_lt (real_of_int x1) y0)))) -> real_lt (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_of_int x2) y0)) (real_of_int x3).
Definition term33 (x0 : int) (x1 : int) := real_lt (real_mul (real_of_int x0) (real_of_int x1)).
Definition term11 := real_le (real_of_num (NUMERAL 0)).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_lt (real_of_int x1) y0)))) -> real_lt (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_of_int x2) y0).
Definition term8 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3)) (real_of_int x0).
Definition term22 (x0 : int) (x1 : int) := and (int_lt x0 x1).
Definition term27 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ (real_lt (real_of_int x2) (real_of_int x3)))).
Definition term37 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := int_lt (int_mul x0 x1) (int_mul x2 x3).
Definition term20 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term21 (x0 : int) (x1 : int) := and (real_lt (real_of_int x0) (real_of_int x1)).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)))) -> real_lt (real_mul (real_of_int x0) y0) (real_mul (real_of_int x1) y1)) (real_of_int x2).
Definition term42 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 y1) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 y3)))) -> int_lt (int_mul y0 y2) (int_mul y1 y3).
Definition term41 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 y0) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 y2)))) -> int_lt (int_mul x0 y1) (int_mul y0 y2).
Definition term40 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 x1) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 y1)))) -> int_lt (int_mul x0 y0) (int_mul x1 y1).
Definition term7 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_lt (real_of_int x1) (real_of_int x3))))) -> real_lt (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_of_int x2) (real_of_int x3)).
Definition term19 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term15 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term34 (x0 : int) (x1 : int) := real_lt (real_of_int (int_mul x0 x1)).
Definition term35 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := real_lt (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_of_int x2) (real_of_int x3)).
Definition term24 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 x1).
Definition term29 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_lt (real_of_int x0) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ (real_lt (real_of_int x2) (real_of_int x3))))).
Definition term14 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term28 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 x1) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 x3))).
Definition term18 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term32 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term16 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term12 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term30 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 x1) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 x3)))).
Definition term36 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := real_lt (real_of_int (int_mul x0 x1)) (real_of_int (int_mul x2 x3)).
Definition term23 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_int x0) (real_of_int x1)).
