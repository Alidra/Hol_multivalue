Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : nat) := @eq int (int_mul (int_of_num (NUMERAL 0)) (int_neg (int_of_num x0))).
Definition term1 (x0 : int) := int_mul x0 (int_of_num (NUMERAL 0)).
Definition term6 (x0 : nat) := @eq int (int_mul (int_of_num (NUMERAL 0)) (int_of_num x0)).
Definition term2 := int_of_num (NUMERAL 0).
Definition term17 (x0 : nat) := @eq int (int_mul (int_neg (int_of_num x0)) (int_of_num (NUMERAL 0))).
Definition term14 (x0 : nat) := @eq int (int_mul (int_of_num x0) (int_of_num (NUMERAL 0))).
Definition term3 (x0 : int) := (fun y0 : int => (int_mul (int_of_num (NUMERAL 0)) y0) = (int_of_num (NUMERAL 0))) x0.
Definition term7 := @eq int (int_of_num (NUMERAL 0)).
Definition term4 (x0 : int) := int_mul (int_of_num (NUMERAL 0)) x0.
Definition term20 (x0 : nat) := ((int_mul (int_of_num (NUMERAL 0)) (int_of_num x0)) = (int_of_num (NUMERAL 0))) /\ (((int_mul (int_of_num (NUMERAL 0)) (int_neg (int_of_num x0))) = (int_of_num (NUMERAL 0))) /\ (((int_mul (int_of_num x0) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) /\ ((int_mul (int_neg (int_of_num x0)) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))))).
Definition term13 (x0 : nat) := int_mul (int_of_num x0) (int_of_num (NUMERAL 0)).
Definition term19 (x0 : nat) := ((int_mul (int_of_num (NUMERAL 0)) (int_neg (int_of_num x0))) = (int_of_num (NUMERAL 0))) /\ (((int_mul (int_of_num x0) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) /\ ((int_mul (int_neg (int_of_num x0)) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0)))).
Definition term5 (x0 : nat) := int_mul (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term9 (x0 : nat) := int_mul (int_of_num (NUMERAL 0)) (int_neg (int_of_num x0)).
Definition term10 (x0 : nat) := int_neg (int_of_num x0).
Definition term15 (x0 : nat) := and ((int_mul (int_of_num x0) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))).
Definition term12 (x0 : nat) := and ((int_mul (int_of_num (NUMERAL 0)) (int_neg (int_of_num x0))) = (int_of_num (NUMERAL 0))).
Definition term0 (x0 : int) := (fun y0 : int => (int_mul y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term18 (x0 : nat) := ((int_mul (int_of_num x0) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) /\ ((int_mul (int_neg (int_of_num x0)) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))).
Definition term8 (x0 : nat) := and ((int_mul (int_of_num (NUMERAL 0)) (int_of_num x0)) = (int_of_num (NUMERAL 0))).
Definition term16 (x0 : nat) := int_mul (int_neg (int_of_num x0)) (int_of_num (NUMERAL 0)).
