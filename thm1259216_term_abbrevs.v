Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add x0 (Nat.add x3 x1)) = (Nat.add (Nat.add (Nat.add x0 (Nat.add (Nat.add x4 x1) (S x2))) x3) x4)) -> False.
