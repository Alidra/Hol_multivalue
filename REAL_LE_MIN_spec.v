Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1562409 : forall x : real, forall y : real, forall z : real, (real_le z (real_min x y)) = ((real_le z x) /\ (real_le z y)).
