Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => (Nat.add (Nat.add x1 y0) x0) = (Nat.add x1 x2)) x3).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Nat.add (Nat.add x2 x0) x1) = (Nat.add x2 x3)).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 y0) x1) = (Nat.add x0 x2)) (Nat.add (Nat.add x1 x2) (S x3)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add x0 (Nat.add (Nat.add x3 x1) (S x2))) x3.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Nat.add (Nat.add x1 y0) x0) = (Nat.add x1 x2).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.add (Nat.add x1 y0) x0) = (Nat.add x1 x2)) x3.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) (S x2).
