Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := forall y0 : int, (int_of_real (real_of_int y0)) = y0.
Definition term0 := forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0).
Definition term2 := (forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0)).
