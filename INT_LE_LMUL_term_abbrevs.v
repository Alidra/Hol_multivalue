Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le x0 x2)) -> int_le (int_mul x1 x0) (int_mul x1 x2).
Definition term24 (x0 : int) (x1 : int) := real_le (real_mul (real_of_int x0) (real_of_int x1)).
Definition term8 := real_of_int (int_of_num (NUMERAL 0)).
Definition term7 := real_of_num (NUMERAL 0).
Definition term15 := int_of_num (NUMERAL 0).
Definition term22 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term20 (x0 : int) (x1 : int) (x2 : int) := imp ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_of_int x1) (real_of_int x2))).
Definition term30 (x0 : int) (x1 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le x0 y0)) -> int_le (int_mul x1 x0) (int_mul x1 y0).
Definition term26 (x0 : int) (x1 : int) (x2 : int) := real_le (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_of_int x1) (real_of_int x2)).
Definition term11 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le y0 y1)) -> real_le (real_mul (real_of_int x0) y0) (real_mul (real_of_int x0) y1)) (real_of_int x1).
Definition term19 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le x1 x2).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le y0 y1)) -> real_le (real_mul (real_of_int x0) y0) (real_mul (real_of_int x0) y1).
Definition term27 (x0 : int) (x1 : int) (x2 : int) := real_le (real_of_int (int_mul x1 x0)) (real_of_int (int_mul x1 x2)).
Definition term9 := real_le (real_of_num (NUMERAL 0)).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_of_int x0) y0)) -> real_le (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_of_int x1) y0).
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) (real_of_int x0).
Definition term32 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2).
Definition term31 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le y0 y1)) -> int_le (int_mul x0 y0) (int_mul x0 y1).
Definition term28 (x0 : int) (x1 : int) (x2 : int) := int_le (int_mul x1 x0) (int_mul x1 x2).
Definition term17 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term25 (x0 : int) (x1 : int) := real_le (real_of_int (int_mul x0 x1)).
Definition term13 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_of_int x0) (real_of_int x2))) -> real_le (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_of_int x1) (real_of_int x2)).
Definition term12 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term16 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term23 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term14 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term21 (x0 : int) (x1 : int) (x2 : int) := imp ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le x1 x2)).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_of_int x0) y0)) -> real_le (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_of_int x1) y0)) (real_of_int x2).
Definition term10 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_of_int x1) (real_of_int x2)).
