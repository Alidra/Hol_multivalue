Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (x0 : int) (x1 : int) := or (int_lt x0 x1).
Definition term5 (x0 : int) := forall y0 : int, (~ (x0 = y0)) = ((int_lt x0 y0) \/ (int_lt y0 x0)).
Definition term19 (x0 : int) (x1 : int) := and ((~ (int_le x1 x0)) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term25 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term13 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (int_le y0 y1)) = (int_lt y1 y0)) x0.
Definition term9 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (int_lt y0 y1)) = (int_le y1 y0)) x0.
Definition term4 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y0 = y1)) = ((int_lt y0 y1) \/ (int_lt y1 y0))) x0.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1)) x0.
Definition term27 (x0 : int) (x1 : int) := @eq Prop ((int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term20 (x0 : int) (x1 : int) := @eq Prop (~ (int_lt x0 x1)).
Definition term29 (x0 : int) (x1 : int) := @eq Prop (int_lt x0 x1).
Definition term30 (x0 : int) (x1 : int) := ((~ (x0 = x1)) = ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0))) /\ ((int_lt x0 x1) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term16 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term15 (x0 : int) (x1 : int) := (fun y0 : int => (~ (int_le x0 y0)) = (int_lt y0 x0)) x1.
Definition term11 (x0 : int) (x1 : int) := (fun y0 : int => (~ (int_lt x0 y0)) = (int_le y0 x0)) x1.
Definition term31 (x0 : int) (x1 : int) := ((~ (int_lt x0 x1)) = (int_le x1 x0)) /\ (((~ (x0 = x1)) = ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0))) /\ ((int_lt x0 x1) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term21 (x0 : int) (x1 : int) := @eq Prop (int_le x0 x1).
Definition term17 (x0 : int) (x1 : int) := @eq Prop (~ (int_le x0 x1)).
Definition term6 (x0 : int) (x1 : int) := (fun y0 : int => (~ (x0 = y0)) = ((int_lt x0 y0) \/ (int_lt y0 x0))) x1.
Definition term3 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term1 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term8 (x0 : int) (x1 : int) := (int_lt x1 x0) \/ (int_lt x0 x1).
Definition term32 (x0 : int) (x1 : int) := ((~ (int_le x0 x1)) = (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0)) /\ (((~ (int_lt x0 x1)) = (int_le x1 x0)) /\ (((~ (x0 = x1)) = ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0))) /\ ((int_lt x0 x1) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)))).
Definition term7 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term14 (x0 : int) := forall y0 : int, (~ (int_le x0 y0)) = (int_lt y0 x0).
Definition term10 (x0 : int) := forall y0 : int, (~ (int_lt x0 y0)) = (int_le y0 x0).
Definition term22 (x0 : int) (x1 : int) := and ((~ (int_lt x1 x0)) = (int_le x0 x1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0)) x1.
Definition term12 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term28 (x0 : int) (x1 : int) := and ((~ (x1 = x0)) = ((int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term26 (x0 : int) (x1 : int) := @eq Prop (~ (x0 = x1)).
Definition term18 (x0 : int) (x1 : int) := @eq Prop (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term24 (x0 : int) (x1 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
