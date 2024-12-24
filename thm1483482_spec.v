Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483482 : forall (a : real) (b : real) (c : real), (real_add (real_add a b) c) = (real_add a (real_add b c)).
