Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := fun y0 : nat => ((num_divides x0 y0) /\ (num_divides y0 x0)) = (x0 = y0).
Definition term3 (x0 : nat) := forall y0 : nat, ((num_divides x0 y0) /\ (num_divides y0 x0)) = (x0 = y0).
Definition term2 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((num_divides x0 y0) /\ (num_divides y0 x0)).
Definition term5 := fun y0 : nat => forall y1 : nat, ((num_divides y0 y1) /\ (num_divides y1 y0)) = (y0 = y1).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((num_divides x0 y0) /\ (num_divides y0 x0))) x1.
Definition term8 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((num_divides y0 y1) /\ (num_divides y1 y0)).
Definition term7 := forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ (num_divides y1 y0)) = (y0 = y1).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((num_divides y0 y1) /\ (num_divides y1 y0))) x0.
Definition term0 (x0 : nat) (x1 : nat) := (num_divides x1 x0) /\ (num_divides x0 x1).
Definition term4 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((num_divides x0 y0) /\ (num_divides y0 x0)).
Definition term6 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((num_divides y0 y1) /\ (num_divides y1 y0)).
