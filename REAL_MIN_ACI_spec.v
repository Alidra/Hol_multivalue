Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1581662 : forall (z : real) (x : real) (y : real), ((real_min x y) = (real_min y x)) /\ (((real_min (real_min x y) z) = (real_min x (real_min y z))) /\ (((real_min x (real_min y z)) = (real_min y (real_min x z))) /\ (((real_min x x) = x) /\ ((real_min x (real_min x y)) = (real_min x y))))).
