Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982759 : forall (a : real) (c : real) (b : real), (real_add (real_add a b) c) = (real_add (real_add a c) b).
