Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) x1.
Definition term6 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 x1) x0) = x1.
Definition term17 (x0 : nat) := Nat.div (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0))).
Definition term31 := @eq nat (S (NUMERAL (BIT1 0))).
Definition term27 := (forall y0 : nat, (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (forall y0 : nat, (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term26 := (forall y0 : nat, (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (forall y0 : nat, (Nat.div (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term36 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term30 := @eq nat (NUMERAL (BIT0 (BIT1 0))).
Definition term21 := fun y0 : nat => (Nat.div (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term4 (x0 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0.
Definition term16 (x0 : nat) := Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term7 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term8 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x1 x0) x1.
Definition term24 := forall y0 : nat, (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term23 := forall y0 : nat, (Nat.div (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term28 (x0 : nat) := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term13 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term25 := and (forall y0 : nat, (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term19 (x0 : nat) := @eq nat (Nat.div (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))).
Definition term20 (x0 : nat) := @eq nat (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term35 := forall y0 : nat, True.
Definition term29 := S (NUMERAL (BIT1 0)).
Definition term34 := fun y0 : nat => True.
Definition term1 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term14 := NUMERAL (BIT0 (BIT1 0)).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term15 (x0 : nat) := Nat.div (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term33 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term18 (x0 : nat) := Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term22 := fun y0 : nat => (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term2 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term37 (x0 : Prop) := forall y0 : nat, x0.
Definition term12 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term32 := NUMERAL (BIT1 0).
