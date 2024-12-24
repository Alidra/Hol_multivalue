Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nat) := ((fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0) -> (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) (S x0).
Definition term37 (x0 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term12 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) (S x0).
Definition term9 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term15 (x0 : nat) := ((real_pow (real_of_num (NUMERAL (BIT1 0))) x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_pow (real_of_num (NUMERAL (BIT1 0))) (S x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term24 := fun y0 : nat => (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0.
Definition term33 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term7 := and ((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term2 := fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term36 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term25 := forall y0 : nat, (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0.
Definition term11 (x0 : nat) := imp ((real_pow (real_of_num (NUMERAL (BIT1 0))) x0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term20 := ((fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) (S y0)).
Definition term35 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term34 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term1 := (((fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0.
Definition term28 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term22 := imp (((fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) (S y0))).
Definition term38 (x0 : nat) := @eq real (real_pow (real_of_num (NUMERAL (BIT1 0))) (S x0)).
Definition term3 := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) (NUMERAL 0).
Definition term18 := forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) (S y0).
Definition term17 := fun y0 : nat => ((real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_pow (real_of_num (NUMERAL (BIT1 0))) (S y0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term31 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term13 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT1 0))) (S x0).
Definition term6 := and ((fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) (NUMERAL 0)).
Definition term16 := fun y0 : nat => ((fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y1) = (real_of_num (NUMERAL (BIT1 0)))) (S y0).
Definition term32 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term21 := ((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_pow (real_of_num (NUMERAL (BIT1 0))) (S y0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term29 := @eq real (real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL 0)).
Definition term5 := real_of_num (NUMERAL (BIT1 0)).
Definition term8 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term30 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term10 (x0 : nat) := imp ((fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term19 := forall y0 : nat, ((real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_pow (real_of_num (NUMERAL (BIT1 0))) (S y0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term27 := (((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_pow (real_of_num (NUMERAL (BIT1 0))) (S y0)) = (real_of_num (NUMERAL (BIT1 0))))) -> forall y0 : nat, (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term4 := real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL 0).
Definition term26 := forall y0 : nat, (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term23 := imp (((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_pow (real_of_num (NUMERAL (BIT1 0))) (S y0)) = (real_of_num (NUMERAL (BIT1 0))))).
