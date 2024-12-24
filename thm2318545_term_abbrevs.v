Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : nat) := (fun y0 : nat => (real_of_int (int_of_num y0)) = (real_of_num y0)) x0.
