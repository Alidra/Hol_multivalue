Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term6 (x0 : real) := real_neg (real_neg x0).
Definition term32 (x0 : nat) (x1 : nat) := and ((real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num (Nat.mul x0 x1)))).
Definition term23 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_of_num x0) (real_of_num x1)).
Definition term22 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term18 (x0 : nat) := real_neg (real_of_num x0).
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term25 (x0 : nat) (x1 : nat) := ((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))) /\ ((real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num (Nat.mul x0 x1))).
Definition term20 (x0 : nat) (x1 : nat) := real_neg (real_mul (real_of_num x0) (real_of_num x1)).
Definition term38 (x0 : nat) (x1 : nat) := ((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))) /\ ((real_neg (real_mul (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num (Nat.mul x0 x1)))).
Definition term26 (x0 : nat) (x1 : nat) := ((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))) /\ ((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))).
Definition term10 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term33 (x0 : nat) (x1 : nat) := and ((real_neg (real_mul (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num (Nat.mul x0 x1)))).
Definition term35 (x0 : nat) (x1 : nat) := ((real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num (Nat.mul x0 x1)))) /\ ((real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num (Nat.mul x0 x1)))).
Definition term40 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_of_num (Nat.mul x0 x1))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0))) x1.
Definition term11 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term24 (x0 : nat) (x1 : nat) := and ((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))).
Definition term34 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_of_num x0) (real_neg (real_of_num x1))).
Definition term39 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.mul x0 x1)).
Definition term29 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term28 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term5 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term8 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term30 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_mul (real_of_num x0) (real_of_num x1))).
Definition term12 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term15 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term19 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_neg (real_of_num x1)).
Definition term13 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term3 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term31 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) x0.
Definition term16 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term1 (x0 : nat) := forall y0 : nat, (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0)).
Definition term27 (x0 : nat) (x1 : nat) := and (((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))) /\ ((real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num (Nat.mul x0 x1)))).
Definition term37 (x0 : nat) (x1 : nat) := (((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))) /\ ((real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num (Nat.mul x0 x1)))) /\ (((real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num (Nat.mul x0 x1)))) /\ ((real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num (Nat.mul x0 x1))))).
Definition term17 (x0 : nat) (x1 : nat) := real_neg (real_mul (real_of_num x0) (real_neg (real_of_num x1))).
Definition term4 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term36 (x0 : nat) (x1 : nat) := ((real_neg (real_mul (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num (Nat.mul x0 x1)))) /\ ((real_neg (real_mul (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num (Nat.mul x0 x1)))).
Definition term21 (x0 : nat) (x1 : nat) := real_neg (real_neg (real_mul (real_of_num x0) (real_of_num x1))).
