Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term9 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term41 (x0 : nat) := @eq Prop (~ (x0 = (NUMERAL 0))).
Definition term6 (x0 : nat) := real_neg (real_of_num x0).
Definition term24 (x0 : nat) (x1 : nat) := ((real_gt (real_of_num x0) (real_of_num x1)) = (Peano.lt x1 x0)) /\ (((real_gt (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.lt x0 x1)) /\ ((real_gt (real_of_num x0) (real_neg (real_of_num x1))) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
Definition term21 (x0 : nat) (x1 : nat) := @eq Prop (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term22 (x0 : nat) (x1 : nat) := ((real_gt (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.lt x0 x1)) /\ ((real_gt (real_of_num x0) (real_neg (real_of_num x1))) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term43 (x0 : nat) := False /\ (x0 = (NUMERAL 0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt y0 x0) = (real_lt x0 y0)) x1.
Definition term36 (x0 : nat) := ~ (False /\ (x0 = (NUMERAL 0))).
Definition term40 (x0 : nat) := @eq Prop (~ (True /\ (x0 = (NUMERAL 0)))).
Definition term25 (x0 : nat) (x1 : nat) := ((real_gt (real_neg (real_of_num x0)) (real_of_num x1)) = False) /\ (((real_gt (real_of_num x0) (real_of_num x1)) = (Peano.lt x1 x0)) /\ (((real_gt (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.lt x0 x1)) /\ ((real_gt (real_of_num x0) (real_neg (real_of_num x1))) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))))).
Definition term10 (x0 : nat) (x1 : nat) := @eq Prop (real_gt (real_of_num x0) (real_of_num x1)).
Definition term7 (x0 : nat) (x1 : nat) := and ((real_gt (real_neg (real_of_num x0)) (real_of_num x1)) = False).
Definition term15 (x0 : nat) (x1 : nat) := @eq Prop (real_gt (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term33 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) (x1 = (NUMERAL 0))).
Definition term1 (x0 : real) := forall y0 : real, (real_gt y0 x0) = (real_lt x0 y0).
Definition term3 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_of_num x0)) (real_of_num x1).
Definition term4 (x0 : nat) (x1 : nat) := ~ (real_gt (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term38 (x0 : nat) := True /\ (x0 = (NUMERAL 0)).
Definition term18 (x0 : nat) (x1 : nat) := real_lt (real_neg (real_of_num x0)) (real_of_num x1).
Definition term28 (x0 : nat) := fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0)).
Definition term39 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term37 (x0 : nat) := ~ ((x0 = (NUMERAL 0)) /\ False).
Definition term17 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_neg (real_of_num x1)).
Definition term11 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term42 (x0 : nat) := (x0 = (NUMERAL 0)) /\ True.
Definition term34 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term44 (x0 : nat) := @eq Prop (~ (False /\ (x0 = (NUMERAL 0)))).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_gt y1 y0) = (real_lt y0 y1)) x0.
Definition term8 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) (x1 = (NUMERAL 0)).
Definition term12 (x0 : nat) (x1 : nat) := and ((real_gt (real_of_num x1) (real_of_num x0)) = (Peano.lt x0 x1)).
Definition term45 (x0 : nat) := (x0 = (NUMERAL 0)) /\ False.
Definition term35 (x0 : nat) := (fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) False.
Definition term14 (x0 : nat) (x1 : nat) := real_lt (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term13 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term30 (x0 : nat) := (fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) True.
Definition term23 (x0 : nat) (x1 : nat) := True /\ ((~ ((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term20 (x0 : nat) (x1 : nat) := @eq Prop (real_gt (real_of_num x0) (real_neg (real_of_num x1))).
Definition term26 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL 0)).
Definition term16 (x0 : nat) (x1 : nat) := and ((real_gt (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.lt x0 x1)).
Definition term31 (x0 : nat) := ~ (True /\ (x0 = (NUMERAL 0))).
Definition term32 (x0 : nat) := ~ ((x0 = (NUMERAL 0)) /\ True).
Definition term27 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) \/ ((x0 = (NUMERAL 0)) = False).
Definition term5 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_neg (real_of_num x1)).
