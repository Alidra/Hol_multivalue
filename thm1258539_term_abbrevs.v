Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : nat) := S (Nat.add x0 (Nat.add x1 x1)).
Definition term4 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term1 (x0 : nat) (x1 : nat) := ~ ((Nat.add (S x0) (Nat.add x1 x1)) = (NUMERAL 0)).
Definition term0 (x0 : nat) (x1 : nat) := ((Nat.add (S x0) (Nat.add x1 x1)) = (NUMERAL 0)) -> False.
Definition term6 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (S x0) (Nat.add x1 x1)).
Definition term2 (x0 : nat) (x1 : nat) := Nat.add (S x0) (Nat.add x1 x1).
Definition term7 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add x0 (Nat.add x1 x1))).
Definition term8 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x1 x1).
Definition term3 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.