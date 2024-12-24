Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term14 (x0 : nat) := (fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) x0.
Definition term1 := real_of_num (NUMERAL 0).
Definition term7 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (x0 = x1)).
Definition term16 (x0 : nat) := @eq real (real_of_num x0).
Definition term8 (x0 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term9 (x0 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_of_num x0))).
Definition term15 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term12 (x0 : nat) := and (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)).
Definition term17 := @eq real (real_of_num (NUMERAL 0)).
Definition term11 (x0 : nat) := ~ ((real_of_num (NUMERAL 0)) = (real_of_num x0)).
Definition term19 := forall y0 : nat, (~ ((real_of_num y0) = (real_of_num (NUMERAL 0)))) = (real_lt (real_of_num (NUMERAL 0)) (real_of_num y0)).
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term10 (x0 : nat) := @eq Prop (~ ((real_of_num x0) = (real_of_num (NUMERAL 0)))).
Definition term3 (x0 : nat) := ~ ((real_of_num x0) = (real_of_num (NUMERAL 0))).
Definition term2 (x0 : nat) := ((real_of_num x0) = (real_of_num (NUMERAL 0))) \/ (~ ((real_of_num x0) = (real_of_num (NUMERAL 0)))).
Definition term13 (x0 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)) /\ (~ ((real_of_num x0) = (real_of_num (NUMERAL 0)))).
Definition term0 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) ((real_of_num x0) = (real_of_num (NUMERAL 0))).
Definition term18 (x0 : nat) := (~ ((real_of_num x0) = (real_of_num (NUMERAL 0)))) -> ((real_of_num x0) = (real_of_num (NUMERAL 0))) = False.
Definition term5 (x0 : real) := forall y0 : real, (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
