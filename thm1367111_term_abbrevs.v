Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (x0 : nat) := @eq real (real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term20 (x0 : nat) := ((real_mul (real_of_num (NUMERAL 0)) (real_of_num x0)) = (real_of_num (NUMERAL 0))) /\ (((real_mul (real_of_num (NUMERAL 0)) (real_neg (real_of_num x0))) = (real_of_num (NUMERAL 0))) /\ (((real_mul (real_of_num x0) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term10 (x0 : nat) := real_neg (real_of_num x0).
Definition term2 := real_of_num (NUMERAL 0).
Definition term18 (x0 : nat) := ((real_mul (real_of_num x0) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term16 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term6 (x0 : nat) := @eq real (real_mul (real_of_num (NUMERAL 0)) (real_of_num x0)).
Definition term7 := @eq real (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term3 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term15 (x0 : nat) := and ((real_mul (real_of_num x0) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term12 (x0 : nat) := and ((real_mul (real_of_num (NUMERAL 0)) (real_neg (real_of_num x0))) = (real_of_num (NUMERAL 0))).
Definition term8 (x0 : nat) := and ((real_mul (real_of_num (NUMERAL 0)) (real_of_num x0)) = (real_of_num (NUMERAL 0))).
Definition term11 (x0 : nat) := @eq real (real_mul (real_of_num (NUMERAL 0)) (real_neg (real_of_num x0))).
Definition term9 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_neg (real_of_num x0)).
Definition term14 (x0 : nat) := @eq real (real_mul (real_of_num x0) (real_of_num (NUMERAL 0))).
Definition term5 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term4 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term19 (x0 : nat) := ((real_mul (real_of_num (NUMERAL 0)) (real_neg (real_of_num x0))) = (real_of_num (NUMERAL 0))) /\ (((real_mul (real_of_num x0) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term1 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).
Definition term13 (x0 : nat) := real_mul (real_of_num x0) (real_of_num (NUMERAL 0)).
