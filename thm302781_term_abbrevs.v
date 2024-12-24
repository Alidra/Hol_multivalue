Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := @eq nat (S (NUMERAL (BIT1 0))).
Definition term5 := or ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term2 := @eq nat (NUMERAL (BIT0 (BIT1 0))).
Definition term9 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term7 (x0 : nat) (x1 : nat) := False \/ (x0 = x1).
Definition term1 := S (NUMERAL (BIT1 0)).
Definition term0 := NUMERAL (BIT0 (BIT1 0)).
Definition term8 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term4 := NUMERAL (BIT1 0).
Definition term6 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (x0 = x1).
