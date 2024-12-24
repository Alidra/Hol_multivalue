Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := @eq nat (S (Nat.add x0 x0)).
Definition term0 (x0 : nat) := S (Nat.add x0 x0).
Definition term1 (x0 : nat) := @eq nat (BIT1 x0).
Definition term4 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term3 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT1 0)).
