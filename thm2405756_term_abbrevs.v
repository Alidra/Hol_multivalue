Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : nat) (x1 : nat) := and (((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))) /\ ((int_mul (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (int_of_num (Nat.mul x0 x1)))).
Definition term28 (x0 : nat) (x1 : nat) := int_mul (int_neg (int_of_num x0)) (int_of_num x1).
Definition term9 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul x0 (int_neg y0)) = (int_neg (int_mul x0 y0))) x1.
Definition term38 (x0 : nat) (x1 : nat) := ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))) /\ ((int_neg (int_mul (int_of_num x0) (int_of_num x1))) = (int_neg (int_of_num (Nat.mul x0 x1)))).
Definition term19 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_neg (int_of_num x1)).
Definition term15 (x0 : int) (x1 : int) := int_mul (int_neg x0) x1.
Definition term33 (x0 : nat) (x1 : nat) := and ((int_neg (int_mul (int_of_num x0) (int_of_num x1))) = (int_neg (int_of_num (Nat.mul x0 x1)))).
Definition term30 (x0 : nat) (x1 : nat) := @eq int (int_neg (int_mul (int_of_num x0) (int_of_num x1))).
Definition term13 (x0 : int) := forall y0 : int, (int_mul (int_neg x0) y0) = (int_neg (int_mul x0 y0)).
Definition term12 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul (int_neg y0) y1) = (int_neg (int_mul y0 y1))) x0.
Definition term7 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul y0 (int_neg y1)) = (int_neg (int_mul y0 y1))) x0.
Definition term36 (x0 : nat) (x1 : nat) := ((int_neg (int_mul (int_of_num x0) (int_of_num x1))) = (int_neg (int_of_num (Nat.mul x0 x1)))) /\ ((int_neg (int_mul (int_of_num x0) (int_of_num x1))) = (int_neg (int_of_num (Nat.mul x0 x1)))).
Definition term24 (x0 : nat) (x1 : nat) := and ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))).
Definition term22 (x0 : nat) (x1 : nat) := @eq int (int_mul (int_neg (int_of_num x0)) (int_neg (int_of_num x1))).
Definition term35 (x0 : nat) (x1 : nat) := ((int_mul (int_neg (int_of_num x0)) (int_of_num x1)) = (int_neg (int_of_num (Nat.mul x0 x1)))) /\ ((int_mul (int_of_num x0) (int_neg (int_of_num x1))) = (int_neg (int_of_num (Nat.mul x0 x1)))).
Definition term40 (x0 : nat) (x1 : nat) := @eq int (int_neg (int_of_num (Nat.mul x0 x1))).
Definition term8 (x0 : int) := forall y0 : int, (int_mul x0 (int_neg y0)) = (int_neg (int_mul x0 y0)).
Definition term37 (x0 : nat) (x1 : nat) := (((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))) /\ ((int_mul (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (int_of_num (Nat.mul x0 x1)))) /\ (((int_mul (int_neg (int_of_num x0)) (int_of_num x1)) = (int_neg (int_of_num (Nat.mul x0 x1)))) /\ ((int_mul (int_of_num x0) (int_neg (int_of_num x1))) = (int_neg (int_of_num (Nat.mul x0 x1))))).
Definition term16 (x0 : nat) (x1 : nat) := int_mul (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term32 (x0 : nat) (x1 : nat) := and ((int_mul (int_neg (int_of_num x0)) (int_of_num x1)) = (int_neg (int_of_num (Nat.mul x0 x1)))).
Definition term20 (x0 : nat) (x1 : nat) := int_neg (int_mul (int_of_num x0) (int_of_num x1)).
Definition term6 (x0 : int) := int_neg (int_neg x0).
Definition term26 (x0 : nat) (x1 : nat) := ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))) /\ ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))).
Definition term25 (x0 : nat) (x1 : nat) := ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))) /\ ((int_mul (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (int_of_num (Nat.mul x0 x1))).
Definition term4 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term5 (x0 : int) := (fun y0 : int => (int_neg (int_neg y0)) = y0) x0.
Definition term11 (x0 : int) (x1 : int) := int_neg (int_mul x0 x1).
Definition term1 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term31 (x0 : nat) (x1 : nat) := int_neg (int_of_num (Nat.mul x0 x1)).
Definition term18 (x0 : nat) := int_neg (int_of_num x0).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0))) x1.
Definition term34 (x0 : nat) (x1 : nat) := @eq int (int_mul (int_of_num x0) (int_neg (int_of_num x1))).
Definition term10 (x0 : int) (x1 : int) := int_mul x0 (int_neg x1).
Definition term21 (x0 : nat) (x1 : nat) := int_neg (int_neg (int_mul (int_of_num x0) (int_of_num x1))).
Definition term17 (x0 : nat) (x1 : nat) := int_neg (int_mul (int_of_num x0) (int_neg (int_of_num x1))).
Definition term29 (x0 : nat) (x1 : nat) := @eq int (int_mul (int_neg (int_of_num x0)) (int_of_num x1)).
Definition term14 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul (int_neg x0) y0) = (int_neg (int_mul x0 y0))) x1.
Definition term39 (x0 : nat) (x1 : nat) := @eq int (int_of_num (Nat.mul x0 x1)).
Definition term3 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term23 (x0 : nat) (x1 : nat) := @eq int (int_mul (int_of_num x0) (int_of_num x1)).
