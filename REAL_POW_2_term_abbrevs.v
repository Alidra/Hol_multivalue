Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 := forall y0 : real, (real_pow y0 (S (S (NUMERAL 0)))) = (real_mul y0 y0).
Definition term20 := forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term30 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 := S (NUMERAL 0).
Definition term2 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term28 := fun y0 : real => True.
Definition term22 (x0 : real) := real_mul x0 (real_pow x0 (S (NUMERAL 0))).
Definition term15 (x0 : real) := real_pow x0 (S (S (NUMERAL 0))).
Definition term5 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term13 := S (S (NUMERAL 0)).
Definition term4 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term3 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term29 := forall y0 : real, True.
Definition term31 (x0 : Prop) := forall y0 : real, x0.
Definition term25 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term27 (x0 : real) := @eq real (real_mul x0 x0).
Definition term14 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term11 := S (NUMERAL (BIT1 0)).
Definition term17 (x0 : real) := @eq real (real_pow x0 (S (S (NUMERAL 0)))).
Definition term6 := S (Nat.add 0 0).
Definition term24 (x0 : real) := real_mul x0 (real_pow x0 (NUMERAL 0)).
Definition term12 := NUMERAL (BIT0 (BIT1 0)).
Definition term19 := fun y0 : real => (real_pow y0 (S (S (NUMERAL 0)))) = (real_mul y0 y0).
Definition term18 := fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term16 (x0 : real) := @eq real (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term26 := real_of_num (NUMERAL (BIT1 0)).
Definition term10 := BIT0 (BIT1 0).
Definition term1 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term23 (x0 : real) := real_pow x0 (S (NUMERAL 0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term9 := S (Nat.add 0 (BIT1 0)).
Definition term8 := NUMERAL (BIT1 0).
