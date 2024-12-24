Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := fun y0 : nat => (real_of_num y0) = (real_of_int (int_of_num y0)).
Definition term0 (x0 : nat) := real_of_int (int_of_num x0).
Definition term4 := forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0)).
Definition term3 := forall y0 : nat, (real_of_int (int_of_num y0)) = (real_of_num y0).
Definition term1 := fun y0 : nat => (real_of_int (int_of_num y0)) = (real_of_num y0).
