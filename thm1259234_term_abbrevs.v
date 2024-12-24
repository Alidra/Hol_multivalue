Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add (Nat.add x2 x0) (Nat.add (Nat.add x3 x0) (S x1))) = (Nat.add x2 x3)) -> False.
