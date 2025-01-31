Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.add x1 x2).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.add x0 x1) x2).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, x0 = (Nat.add (Nat.add x1 x2) (S y0)).
Definition term3 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (exists y0 : nat, x0 = (Nat.add (Nat.add x1 x2) (S y0))).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add x0 x1) x2.
