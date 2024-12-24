Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Nat.add y0 x0) = (Nat.add (Nat.add x3 x1) x2)) (Nat.add x3 x4).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((Nat.add x0 x1) = (Nat.add (Nat.add x2 x3) x4)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((fun y0 : nat => (Nat.add y0 x0) = (Nat.add (Nat.add x1 x2) x3)) x4).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (Nat.add y0 x0) = (Nat.add (Nat.add x1 x2) x3).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Nat.add y0 x0) = (Nat.add (Nat.add x1 x2) x3)) x4.
