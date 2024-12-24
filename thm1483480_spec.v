Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483480 : forall (a : real) (c : real) (b : real) (d : real), (real_add (real_add a b) (real_add c d)) = (real_add (real_add a c) (real_add b d)).
