Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0))) x1.
Definition term2 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub x0 x1).
Definition term1 (x0 : nat) (x1 : nat) := Nat.sub x0 (S x1).
