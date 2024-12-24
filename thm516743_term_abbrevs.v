Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 y0))) x2.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 x2).
