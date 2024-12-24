Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
