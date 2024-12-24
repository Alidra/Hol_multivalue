Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1355147 : forall x : real, forall y : real, forall z : real, ((real_add x z) = (real_add y z)) = (x = y).
