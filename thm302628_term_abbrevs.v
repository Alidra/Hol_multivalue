Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term2 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term1 (x0 : nat) := @eq nat (Nat.add x0 x0).
Definition term3 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
