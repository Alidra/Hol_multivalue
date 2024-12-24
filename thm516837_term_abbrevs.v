Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = 0) = ((x0 = 0) \/ (y0 = 0))) x1.
Definition term1 (x0 : nat) (x1 : nat) := (x0 = 0) \/ (x1 = 0).
