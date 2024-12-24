Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, (int_le (int_of_num y0) (int_of_num y1)) = (Peano.le y0 y1).
