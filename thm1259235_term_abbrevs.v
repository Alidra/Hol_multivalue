Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x1 (Nat.add (Nat.add x3 x2) (S x0))) = (Nat.add (Nat.add x1 x2) x3)) -> False.
