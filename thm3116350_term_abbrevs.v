Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((num_divides x0 y0) /\ (num_divides y0 x0))) x1.
Definition term1 (x0 : nat) (x1 : nat) := (num_divides x1 x0) /\ (num_divides x0 x1).
