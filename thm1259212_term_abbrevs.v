Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : nat) := S (Nat.add x0 (Nat.add x1 x1)).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add (Nat.add x2 (Nat.add (Nat.add x4 x1) (S x0))) (Nat.add x3 x1)) = (Nat.add (Nat.add x2 x3) x4)) -> False.
Definition term4 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term1 (x0 : nat) (x1 : nat) := ~ ((Nat.add (S x0) (Nat.add x1 x1)) = (NUMERAL 0)).
Definition term0 (x0 : nat) (x1 : nat) := ((Nat.add (S x0) (Nat.add x1 x1)) = (NUMERAL 0)) -> False.
Definition term6 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (S x0) (Nat.add x1 x1)).
Definition term2 (x0 : nat) (x1 : nat) := Nat.add (S x0) (Nat.add x1 x1).
Definition term7 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add x0 (Nat.add x1 x1))).
Definition term8 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x1 x1).
Definition term3 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
