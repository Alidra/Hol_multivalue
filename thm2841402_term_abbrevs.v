Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (int_lt (int_of_num x0) (int_of_num y0))) x1.
