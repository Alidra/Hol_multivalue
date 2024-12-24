Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 := @eq int (int_of_num (NUMERAL (BIT1 0))).
Definition term10 (x0 : int) := @eq real (real_of_int (int_pow x0 (NUMERAL 0))).
Definition term27 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term42 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term32 (x0 : int) := forall y0 : nat, (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0)).
Definition term0 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term3 := forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term29 (x0 : int) (x1 : nat) := real_of_int (int_mul x0 (int_pow x0 x1)).
Definition term1 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term16 := forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1)).
Definition term31 (x0 : int) (x1 : nat) := int_mul x0 (int_pow x0 x1).
Definition term24 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow x0 (S x1))).
Definition term20 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) (S x1).
Definition term11 (x0 : nat) := real_of_int (int_of_num x0).
Definition term17 (x0 : int) := (fun y0 : real => forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1))) (real_of_int x0).
Definition term44 (x0 : int) := ((int_pow x0 (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0))).
Definition term22 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 (S x1)).
Definition term19 (x0 : int) (x1 : nat) := (fun y0 : nat => (real_pow (real_of_int x0) (S y0)) = (real_mul (real_of_int x0) (real_pow (real_of_int x0) y0))) x1.
Definition term9 (x0 : int) := @eq real (real_pow (real_of_int x0) (NUMERAL 0)).
Definition term38 (x0 : int) (x1 : nat) := @eq int (int_mul x0 (int_pow x0 x1)).
Definition term5 (x0 : int) := real_pow (real_of_int x0) (NUMERAL 0).
Definition term39 (x0 : int) := fun y0 : nat => (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0)).
Definition term41 := forall y0 : nat, True.
Definition term14 (x0 : int) := int_pow x0 (NUMERAL 0).
Definition term33 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0))) x1.
Definition term6 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term26 (x0 : int) (x1 : nat) := real_mul (real_of_int x0) (real_of_int (int_pow x0 x1)).
Definition term40 := fun y0 : nat => True.
Definition term18 (x0 : int) := forall y0 : nat, (real_pow (real_of_int x0) (S y0)) = (real_mul (real_of_int x0) (real_pow (real_of_int x0) y0)).
Definition term37 (x0 : int) (x1 : nat) := @eq int (int_pow x0 (S x1)).
Definition term8 (x0 : int) := real_of_int (int_pow x0 (NUMERAL 0)).
Definition term30 (x0 : int) (x1 : nat) := int_pow x0 (S x1).
Definition term34 (x0 : int) := @eq int (int_pow x0 (NUMERAL 0)).
Definition term4 (x0 : int) := (fun y0 : real => (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term2 := real_of_num (NUMERAL (BIT1 0)).
Definition term23 (x0 : int) (x1 : nat) := @eq real (real_pow (real_of_int x0) (S x1)).
Definition term43 (x0 : Prop) := forall y0 : nat, x0.
Definition term28 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term12 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term7 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term36 (x0 : int) := and ((int_pow x0 (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term25 (x0 : int) := real_mul (real_of_int x0).
Definition term15 := int_of_num (NUMERAL (BIT1 0)).
Definition term21 (x0 : int) (x1 : nat) := real_mul (real_of_int x0) (real_pow (real_of_int x0) x1).
Definition term13 := NUMERAL (BIT1 0).
