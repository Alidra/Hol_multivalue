Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1578322 : forall (z : real) (x : real) (y : real), ((real_max x y) = (real_max y x)) /\ (((real_max (real_max x y) z) = (real_max x (real_max y z))) /\ (((real_max x (real_max y z)) = (real_max y (real_max x z))) /\ (((real_max x x) = x) /\ ((real_max x (real_max x y)) = (real_max x y))))).
