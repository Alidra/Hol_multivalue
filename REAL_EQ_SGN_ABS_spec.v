Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1720940 : forall x : real, forall y : real, (x = y) = (((real_sgn x) = (real_sgn y)) /\ ((real_abs x) = (real_abs y))).
