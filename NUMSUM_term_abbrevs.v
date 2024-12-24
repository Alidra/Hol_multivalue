Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : Prop) := fun y0 : nat => @COND nat x0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term5 (x0 : Prop) := forall y0 : nat, (NUMSUM x0 y0) = (@COND nat x0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term0 := fun y0 : Prop => fun y1 : nat => @COND nat y0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1).
Definition term4 (x0 : Prop) (x1 : nat) := @COND nat x0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term1 (x0 : Prop) := (fun y0 : Prop => fun y1 : nat => @COND nat y0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) x0.
Definition term6 := forall y0 : Prop, forall y1 : nat, (NUMSUM y0 y1) = (@COND nat y0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)).
Definition term3 (x0 : Prop) (x1 : nat) := (fun y0 : nat => @COND nat x0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1.
Definition term8 (x0 : Prop) (x1 : nat) := (fun y0 : nat => (NUMSUM x0 y0) = (@COND nat x0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) x1.
Definition term7 (x0 : Prop) := (fun y0 : Prop => forall y1 : nat, (NUMSUM y0 y1) = (@COND nat y0 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) x0.
