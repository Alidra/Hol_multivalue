Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt y1 y2))) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt y0 y1))) x1.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 y0))) x2.
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt y0 y1)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 y0)).