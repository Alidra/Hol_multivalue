Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1565427 : forall x : real, forall y : real, forall z : real, (real_lt z (real_min x y)) = ((real_lt z x) /\ (real_lt z y)).