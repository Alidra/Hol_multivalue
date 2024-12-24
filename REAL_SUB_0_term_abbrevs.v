Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term47 (x0 : real) := forall y0 : real, ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term24 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term23 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term32 := real_of_num (NUMERAL 0).
Definition term20 (x0 : real) (x1 : real) := (fun y0 : real => (real_le y0 x0) = (~ (real_lt x0 y0))) x1.
Definition term40 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 x1))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term31 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term10 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_le y0 x0)) x1.
Definition term44 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x0 x1)) /\ (real_le x0 x1)).
Definition term48 := forall y0 : real, forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1).
Definition term29 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term28 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term18 := forall y0 : real, forall y1 : real, (real_le y1 y0) = (~ (real_lt y0 y1)).
Definition term17 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term33 (x0 : real) (x1 : real) := (real_le (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term12 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term11 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term27 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term21 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term1 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term3 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term7 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term39 (x0 : real) (x1 : real) := and (~ (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 x1))).
Definition term37 (x0 : real) (x1 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term6 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_lt y0 x0)) x1.
Definition term26 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term15 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term9 (x0 : real) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_le y0 x0).
Definition term5 (x0 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_lt y0 x0).
Definition term30 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y1 y0) = (~ (real_lt y0 y1))) x0.
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_le y1 y0)) x0.
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_lt y1 y0)) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) x0.
Definition term42 (x0 : real) (x1 : real) := and (~ (real_lt x0 x1)).
Definition term22 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term14 (x0 : real) := forall y0 : real, (real_le y0 x0) = (~ (real_lt x0 y0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) = (real_le y0 x0)) x1.
Definition term35 (x0 : real) (x1 : real) := @eq Prop ((real_le (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1))).
Definition term43 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) /\ (real_le x0 x1).
Definition term13 (x0 : real) := fun y0 : real => (real_le y0 x0) = (~ (real_lt x0 y0)).
Definition term45 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term34 (x0 : real) (x1 : real) := @eq Prop ((real_sub x0 x1) = (real_of_num (NUMERAL 0))).
Definition term36 (x0 : real) (x1 : real) := real_le (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term25 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term46 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term41 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 x1))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1))).
Definition term38 (x0 : real) (x1 : real) := and (real_le (real_sub x0 x1) (real_of_num (NUMERAL 0))).
Definition term16 := fun y0 : real => forall y1 : real, (real_le y1 y0) = (~ (real_lt y0 y1)).
