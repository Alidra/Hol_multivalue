Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) (x1 : nat) := real_ge (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term5 (x0 : nat) := real_neg (real_of_num x0).
Definition term35 (x0 : nat) := False /\ (x0 = (NUMERAL 0)).
Definition term28 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) (x1 = (NUMERAL 0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge y0 x0) = (real_le x0 y0)) x1.
Definition term13 (x0 : nat) (x1 : nat) := real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term20 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term17 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term9 (x0 : nat) (x1 : nat) := @eq Prop (real_ge (real_of_num x0) (real_of_num x1)).
Definition term11 (x0 : nat) (x1 : nat) := and ((real_ge (real_of_num x1) (real_of_num x0)) = (Peano.le x0 x1)).
Definition term1 (x0 : real) := forall y0 : real, (real_ge y0 x0) = (real_le x0 y0).
Definition term30 (x0 : nat) := True /\ (x0 = (NUMERAL 0)).
Definition term27 (x0 : nat) := fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0).
Definition term3 (x0 : nat) (x1 : nat) := real_ge (real_of_num x0) (real_neg (real_of_num x1)).
Definition term39 (x0 : nat) := @eq Prop (False /\ (x0 = (NUMERAL 0))).
Definition term37 (x0 : nat) := @eq Prop (True /\ (x0 = (NUMERAL 0))).
Definition term18 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term16 (x0 : nat) (x1 : nat) := real_ge (real_neg (real_of_num x0)) (real_of_num x1).
Definition term32 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) (x1 = (NUMERAL 0))).
Definition term19 (x0 : nat) (x1 : nat) := @eq Prop (real_ge (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term4 (x0 : nat) (x1 : nat) := real_le (real_neg (real_of_num x0)) (real_of_num x1).
Definition term31 (x0 : nat) := (x0 = (NUMERAL 0)) /\ True.
Definition term33 (x0 : nat) (x1 : nat) := @eq Prop (((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_ge y1 y0) = (real_le y0 y1)) x0.
Definition term15 (x0 : nat) (x1 : nat) := and ((real_ge (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.le x0 x1)).
Definition term6 (x0 : nat) (x1 : nat) := and ((real_ge (real_of_num x0) (real_neg (real_of_num x1))) = True).
Definition term10 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term36 (x0 : nat) := (x0 = (NUMERAL 0)) /\ False.
Definition term21 (x0 : nat) (x1 : nat) := ((real_ge (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.le x0 x1)) /\ ((real_ge (real_neg (real_of_num x0)) (real_of_num x1)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term24 (x0 : nat) (x1 : nat) := ((real_ge (real_of_num x0) (real_neg (real_of_num x1))) = True) /\ (((real_ge (real_of_num x0) (real_of_num x1)) = (Peano.le x1 x0)) /\ (((real_ge (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.le x0 x1)) /\ ((real_ge (real_neg (real_of_num x0)) (real_of_num x1)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
Definition term14 (x0 : nat) (x1 : nat) := @eq Prop (real_ge (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term22 (x0 : nat) (x1 : nat) := True /\ (((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term34 (x0 : nat) := (fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) False.
Definition term25 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL 0)).
Definition term23 (x0 : nat) (x1 : nat) := ((real_ge (real_of_num x0) (real_of_num x1)) = (Peano.le x1 x0)) /\ (((real_ge (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.le x0 x1)) /\ ((real_ge (real_neg (real_of_num x0)) (real_of_num x1)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term8 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term7 (x0 : nat) (x1 : nat) := real_ge (real_of_num x0) (real_of_num x1).
Definition term29 (x0 : nat) := (fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) True.
Definition term38 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term26 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) \/ ((x0 = (NUMERAL 0)) = False).
