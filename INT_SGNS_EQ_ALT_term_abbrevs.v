Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 (x0 : int) (x1 : int) := ((x0 = (int_of_num (NUMERAL 0))) -> x1 = (int_of_num (NUMERAL 0))) /\ (((int_gt x0 (int_of_num (NUMERAL 0))) -> int_gt x1 (int_of_num (NUMERAL 0))) /\ ((int_lt x0 (int_of_num (NUMERAL 0))) -> int_lt x1 (int_of_num (NUMERAL 0)))).
Definition term3 (x0 : int) := real_sgn (real_of_int x0).
Definition term12 := real_of_int (int_of_num (NUMERAL 0)).
Definition term24 (x0 : int) (x1 : int) := real_gt (real_of_int x0) (real_of_int x1).
Definition term11 := real_of_num (NUMERAL 0).
Definition term40 (x0 : int) (x1 : int) := (int_lt x0 (int_of_num (NUMERAL 0))) -> int_lt x1 (int_of_num (NUMERAL 0)).
Definition term14 := int_of_num (NUMERAL 0).
Definition term36 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term33 (x0 : int) := real_lt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term16 (x0 : int) := imp (x0 = (int_of_num (NUMERAL 0))).
Definition term21 (x0 : int) := real_gt (real_of_int x0).
Definition term27 (x0 : int) := imp (int_gt x0 (int_of_num (NUMERAL 0))).
Definition term41 (x0 : int) (x1 : int) := ((real_gt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_gt (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_lt (real_of_int x1) (real_of_num (NUMERAL 0))).
Definition term18 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) -> x1 = (int_of_num (NUMERAL 0)).
Definition term23 (x0 : int) := real_gt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term22 (x0 : int) := real_gt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => ((real_sgn (real_of_int x0)) = (real_sgn y0)) = ((((real_of_int x0) = (real_of_num (NUMERAL 0))) -> y0 = (real_of_num (NUMERAL 0))) /\ (((real_gt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_gt y0 (real_of_num (NUMERAL 0))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_lt y0 (real_of_num (NUMERAL 0)))))) (real_of_int x1).
Definition term7 (x0 : int) := @eq real (real_of_int (int_sgn x0)).
Definition term38 (x0 : int) := imp (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term10 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, ((real_sgn y0) = (real_sgn y1)) = (((y0 = (real_of_num (NUMERAL 0))) -> y1 = (real_of_num (NUMERAL 0))) /\ (((real_gt y0 (real_of_num (NUMERAL 0))) -> real_gt y1 (real_of_num (NUMERAL 0))) /\ ((real_lt y0 (real_of_num (NUMERAL 0))) -> real_lt y1 (real_of_num (NUMERAL 0)))))) (real_of_int x0).
Definition term35 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, ((real_sgn (real_of_int x0)) = (real_sgn y0)) = ((((real_of_int x0) = (real_of_num (NUMERAL 0))) -> y0 = (real_of_num (NUMERAL 0))) /\ (((real_gt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_gt y0 (real_of_num (NUMERAL 0))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_lt y0 (real_of_num (NUMERAL 0))))).
Definition term42 (x0 : int) (x1 : int) := ((int_gt x0 (int_of_num (NUMERAL 0))) -> int_gt x1 (int_of_num (NUMERAL 0))) /\ ((int_lt x0 (int_of_num (NUMERAL 0))) -> int_lt x1 (int_of_num (NUMERAL 0))).
Definition term4 (x0 : int) (x1 : int) := (((real_of_int x0) = (real_of_num (NUMERAL 0))) -> (real_of_int x1) = (real_of_num (NUMERAL 0))) /\ (((real_gt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_gt (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_lt (real_of_int x1) (real_of_num (NUMERAL 0)))).
Definition term37 (x0 : int) := imp (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term44 (x0 : int) := forall y0 : int, ((int_sgn x0) = (int_sgn y0)) = (((x0 = (int_of_num (NUMERAL 0))) -> y0 = (int_of_num (NUMERAL 0))) /\ (((int_gt x0 (int_of_num (NUMERAL 0))) -> int_gt y0 (int_of_num (NUMERAL 0))) /\ ((int_lt x0 (int_of_num (NUMERAL 0))) -> int_lt y0 (int_of_num (NUMERAL 0))))).
Definition term31 (x0 : int) (x1 : int) := and ((int_gt x0 (int_of_num (NUMERAL 0))) -> int_gt x1 (int_of_num (NUMERAL 0))).
Definition term34 (x0 : int) := real_lt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term45 := forall y0 : int, forall y1 : int, ((int_sgn y0) = (int_sgn y1)) = (((y0 = (int_of_num (NUMERAL 0))) -> y1 = (int_of_num (NUMERAL 0))) /\ (((int_gt y0 (int_of_num (NUMERAL 0))) -> int_gt y1 (int_of_num (NUMERAL 0))) /\ ((int_lt y0 (int_of_num (NUMERAL 0))) -> int_lt y1 (int_of_num (NUMERAL 0))))).
Definition term20 (x0 : int) (x1 : int) := and ((x0 = (int_of_num (NUMERAL 0))) -> x1 = (int_of_num (NUMERAL 0))).
Definition term5 (x0 : int) := real_of_int (int_sgn x0).
Definition term6 (x0 : int) := @eq real (real_sgn (real_of_int x0)).
Definition term25 (x0 : int) := int_gt x0 (int_of_num (NUMERAL 0)).
Definition term17 (x0 : int) (x1 : int) := ((real_of_int x0) = (real_of_num (NUMERAL 0))) -> (real_of_int x1) = (real_of_num (NUMERAL 0)).
Definition term26 (x0 : int) := imp (real_gt (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term28 (x0 : int) (x1 : int) := (real_gt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_gt (real_of_int x1) (real_of_num (NUMERAL 0)).
Definition term39 (x0 : int) (x1 : int) := (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_lt (real_of_int x1) (real_of_num (NUMERAL 0)).
Definition term9 (x0 : int) (x1 : int) := @eq Prop ((int_sgn x0) = (int_sgn x1)).
Definition term19 (x0 : int) (x1 : int) := and (((real_of_int x0) = (real_of_num (NUMERAL 0))) -> (real_of_int x1) = (real_of_num (NUMERAL 0))).
Definition term32 (x0 : int) := real_lt (real_of_int x0).
Definition term15 (x0 : int) := imp ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term13 (x0 : int) := @eq real (real_of_int x0).
Definition term8 (x0 : int) (x1 : int) := @eq Prop ((real_sgn (real_of_int x0)) = (real_sgn (real_of_int x1))).
Definition term30 (x0 : int) (x1 : int) := and ((real_gt (real_of_int x0) (real_of_num (NUMERAL 0))) -> real_gt (real_of_int x1) (real_of_num (NUMERAL 0))).
Definition term29 (x0 : int) (x1 : int) := (int_gt x0 (int_of_num (NUMERAL 0))) -> int_gt x1 (int_of_num (NUMERAL 0)).
