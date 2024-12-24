Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term32 (x0 : int) (x1 : int) (x2 : nat) := int_lt (int_pow x0 x2) (int_pow x1 x2).
Definition term8 := real_of_int (int_of_num (NUMERAL 0)).
Definition term7 := real_of_num (NUMERAL 0).
Definition term15 := int_of_num (NUMERAL 0).
Definition term25 (x0 : nat) (x1 : int) (x2 : int) := imp ((~ (x0 = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 x2))).
Definition term24 (x0 : nat) (x1 : int) (x2 : int) := imp ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_lt (real_of_int x1) (real_of_int x2)))).
Definition term31 (x0 : int) (x1 : int) (x2 : nat) := real_lt (real_of_int (int_pow x0 x2)) (real_of_int (int_pow x1 x2)).
Definition term34 (x0 : int) (x1 : nat) := forall y0 : int, ((~ (x1 = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 y0))) -> int_lt (int_pow x0 x1) (int_pow y0 x1).
Definition term11 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term2 (x0 : nat) (x1 : int) := (fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0)) (real_of_int x1).
Definition term1 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term9 := real_le (real_of_num (NUMERAL 0)).
Definition term3 (x0 : int) (x1 : nat) := forall y0 : real, ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_int x0) y0))) -> real_lt (real_pow (real_of_int x0) x1) (real_pow y0 x1).
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term18 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term36 := forall y0 : nat, forall y1 : int, forall y2 : int, ((~ (y0 = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 y2))) -> int_lt (int_pow y1 y0) (int_pow y2 y0).
Definition term23 (x0 : nat) (x1 : int) (x2 : int) := (~ (x0 = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 x2)).
Definition term28 (x0 : int) (x1 : nat) := real_lt (real_pow (real_of_int x0) x1).
Definition term35 (x0 : nat) := forall y0 : int, forall y1 : int, ((~ (x0 = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 y1))) -> int_lt (int_pow y0 x0) (int_pow y1 x0).
Definition term26 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term29 (x0 : int) (x1 : nat) := real_lt (real_of_int (int_pow x0 x1)).
Definition term5 (x0 : int) (x1 : int) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_int x0) (real_of_int x1)))) -> real_lt (real_pow (real_of_int x0) x2) (real_pow (real_of_int x1) x2).
Definition term21 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term17 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term33 (x0 : int) (x1 : int) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 x1))) -> int_lt (int_pow x0 x2) (int_pow x1 x2).
Definition term13 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term20 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 x1).
Definition term12 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term16 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term30 (x0 : int) (x1 : int) (x2 : nat) := real_lt (real_pow (real_of_int x0) x2) (real_pow (real_of_int x1) x2).
Definition term14 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term27 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term4 (x0 : int) (x1 : nat) (x2 : int) := (fun y0 : real => ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_int x0) y0))) -> real_lt (real_pow (real_of_int x0) x1) (real_pow y0 x1)) (real_of_int x2).
Definition term10 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term19 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_int x0) (real_of_int x1)).
Definition term22 (x0 : nat) (x1 : int) (x2 : int) := (~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_lt (real_of_int x1) (real_of_int x2))).
