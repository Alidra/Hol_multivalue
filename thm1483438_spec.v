Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483438 : forall (a : real) (b : real) (m : real), (real_add (real_mul a m) (real_mul b m)) = (real_mul (real_add a b) m).
