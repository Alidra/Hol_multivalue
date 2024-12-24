Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1557480 : forall x : real, forall y : real, (real_le x (real_max x y)) /\ (real_le y (real_max x y)).
