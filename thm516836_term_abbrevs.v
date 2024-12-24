Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = 0) = ((x0 = 0) \/ (y0 = 0))) x1.
Definition term1 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = 0) = ((x0 = 0) \/ (y0 = 0)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = 0) = ((y0 = 0) \/ (y1 = 0))) x0.
