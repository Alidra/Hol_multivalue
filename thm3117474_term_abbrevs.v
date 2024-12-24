Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((int_of_num x0) = (int_of_num y0))) x1.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((int_of_num y0) = (int_of_num y1))) x0.
Definition term1 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((int_of_num x0) = (int_of_num y0)).
