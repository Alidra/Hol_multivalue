Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483490 : forall (a : real) (c : real) (d : real), (real_add a (real_add c d)) = (real_add (real_add a c) d).
