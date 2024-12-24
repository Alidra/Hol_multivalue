Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := int_abs (int_of_num x0).
Definition term0 (x0 : nat) (x1 : nat) := ~ (~ (((int_of_num x0) = (int_of_num x1)) = ((int_abs (int_of_num x0)) = (int_abs (int_of_num x1))))).
