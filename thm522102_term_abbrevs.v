Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).