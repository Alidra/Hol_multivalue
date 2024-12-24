Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.sub x1 x2).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.sub x0 y0)) = (Nat.sub (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
