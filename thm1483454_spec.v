Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483454 : forall (a : real) (b : real) (c : real), (real_mul (real_add a b) c) = (real_add (real_mul a c) (real_mul b c)).
