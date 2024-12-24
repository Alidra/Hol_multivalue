Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305242 : forall (z : int) (x : int) (y : int), ((int_max x y) = (int_max y x)) /\ (((int_max (int_max x y) z) = (int_max x (int_max y z))) /\ (((int_max x (int_max y z)) = (int_max y (int_max x z))) /\ (((int_max x x) = x) /\ ((int_max x (int_max x y)) = (int_max x y))))).
