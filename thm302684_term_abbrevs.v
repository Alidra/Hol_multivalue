Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term1 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term3 := NUMERAL (BIT0 (BIT1 0)).
Definition term4 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term2 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (x0 = x1).
