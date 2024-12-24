Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305588 : forall (z : int) (x : int) (y : int), ((int_min x y) = (int_min y x)) /\ (((int_min (int_min x y) z) = (int_min x (int_min y z))) /\ (((int_min x (int_min y z)) = (int_min y (int_min x z))) /\ (((int_min x x) = x) /\ ((int_min x (int_min x y)) = (int_min x y))))).
