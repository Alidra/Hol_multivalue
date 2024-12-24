Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term1 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
