Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301668 : forall x : int, forall y : int, forall z : int, ((~ (z = (int_of_num (NUMERAL 0)))) /\ ((int_mul z x) = (int_mul z y))) -> x = y.
