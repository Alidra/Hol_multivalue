Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1559391 : forall x : real, forall y : real, (real_min x y) = (real_min y x).
