Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 (x0 : int) (x1 : int) := ((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x1))) \/ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_int x1) (real_of_num (NUMERAL 0)))).
Definition term39 (x0 : int) (x1 : int) := (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_int x1) (real_of_num (NUMERAL 0))).
Definition term7 := real_of_int (int_of_num (NUMERAL 0)).
Definition term6 := real_of_num (NUMERAL 0).
Definition term24 (x0 : int) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term29 (x0 : int) (x1 : int) := (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x1)).
Definition term15 := int_of_num (NUMERAL 0).
Definition term10 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term36 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term34 (x0 : int) := real_lt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term3 (x0 : int) (x1 : int) := real_le (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term4 (x0 : int) (x1 : int) := ((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ (((real_of_int x1) = (real_of_num (NUMERAL 0))) \/ (((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x1))) \/ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_int x1) (real_of_num (NUMERAL 0)))))).
Definition term31 (x0 : int) (x1 : int) := or ((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x1))).
Definition term38 (x0 : int) := and (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term45 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ ((x1 = (int_of_num (NUMERAL 0))) \/ (((int_lt (int_of_num (NUMERAL 0)) x0) /\ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ ((int_lt x0 (int_of_num (NUMERAL 0))) /\ (int_lt x1 (int_of_num (NUMERAL 0)))))).
Definition term12 (x0 : int) (x1 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_mul x0 x1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) y0)) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ ((y0 = (real_of_num (NUMERAL 0))) \/ (((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_lt y0 (real_of_num (NUMERAL 0)))))))) (real_of_int x1).
Definition term8 := real_le (real_of_num (NUMERAL 0)).
Definition term21 := real_lt (real_of_num (NUMERAL 0)).
Definition term5 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) = ((y0 = (real_of_num (NUMERAL 0))) \/ ((y1 = (real_of_num (NUMERAL 0))) \/ (((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ ((real_lt y0 (real_of_num (NUMERAL 0))) /\ (real_lt y1 (real_of_num (NUMERAL 0)))))))) (real_of_int x0).
Definition term26 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term25 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) y0)) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) \/ ((y0 = (real_of_num (NUMERAL 0))) \/ (((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_lt y0 (real_of_num (NUMERAL 0))))))).
Definition term30 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) /\ (int_lt (int_of_num (NUMERAL 0)) x1).
Definition term46 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) (int_mul x0 y0)) = ((x0 = (int_of_num (NUMERAL 0))) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (((int_lt (int_of_num (NUMERAL 0)) x0) /\ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ ((int_lt x0 (int_of_num (NUMERAL 0))) /\ (int_lt y0 (int_of_num (NUMERAL 0))))))).
Definition term32 (x0 : int) (x1 : int) := or ((int_lt (int_of_num (NUMERAL 0)) x0) /\ (int_lt (int_of_num (NUMERAL 0)) x1)).
Definition term35 (x0 : int) := real_lt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term47 := forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) (int_mul y0 y1)) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (((int_lt (int_of_num (NUMERAL 0)) y0) /\ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ ((int_lt y0 (int_of_num (NUMERAL 0))) /\ (int_lt y1 (int_of_num (NUMERAL 0))))))).
Definition term27 (x0 : int) := and (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term22 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term23 (x0 : int) := real_lt (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term17 (x0 : int) (x1 : int) := @eq Prop (int_le (int_of_num (NUMERAL 0)) (int_mul x0 x1)).
Definition term13 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term44 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (((int_lt (int_of_num (NUMERAL 0)) x0) /\ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ ((int_lt x0 (int_of_num (NUMERAL 0))) /\ (int_lt x1 (int_of_num (NUMERAL 0))))).
Definition term40 (x0 : int) (x1 : int) := (int_lt x0 (int_of_num (NUMERAL 0))) /\ (int_lt x1 (int_of_num (NUMERAL 0))).
Definition term28 (x0 : int) := and (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term19 (x0 : int) := or ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term37 (x0 : int) := and (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term43 (x0 : int) (x1 : int) := ((real_of_int x1) = (real_of_num (NUMERAL 0))) \/ (((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x1))) \/ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_int x1) (real_of_num (NUMERAL 0))))).
Definition term14 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_mul x0 x1).
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term33 (x0 : int) := real_lt (real_of_int x0).
Definition term18 (x0 : int) := @eq real (real_of_int x0).
Definition term20 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term9 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term42 (x0 : int) (x1 : int) := ((int_lt (int_of_num (NUMERAL 0)) x0) /\ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ ((int_lt x0 (int_of_num (NUMERAL 0))) /\ (int_lt x1 (int_of_num (NUMERAL 0)))).
Definition term16 (x0 : int) (x1 : int) := @eq Prop (real_le (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) (real_of_int x1))).
