Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982757 : forall (c : real) (a : real) (d : real), (real_add a (real_add c d)) = (real_add c (real_add a d)).
