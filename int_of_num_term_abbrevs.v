Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := int_of_real (real_of_num x0).
Definition term0 := fun y0 : nat => int_of_real (real_of_num y0).
Definition term3 := forall y0 : nat, (int_of_num y0) = (int_of_real (real_of_num y0)).
Definition term1 (x0 : nat) := (fun y0 : nat => int_of_real (real_of_num y0)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => (int_of_num y0) = (int_of_real (real_of_num y0))) x0.
