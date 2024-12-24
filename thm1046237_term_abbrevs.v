Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Nat.add (Nat.mul x0 x3) (Nat.mul x2 x1)) = (Nat.add (Nat.mul x0 x1) (Nat.mul x2 x3))).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((~ (x0 = x1)) /\ (~ (x2 = y0))) = (~ ((Nat.add (Nat.mul x0 x2) (Nat.mul x1 y0)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 x2))))) x3.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) /\ (~ (x2 = x3)).
