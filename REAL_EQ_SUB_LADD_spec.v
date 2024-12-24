Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1521519 : forall x : real, forall y : real, forall z : real, (x = (real_sub y z)) = ((real_add x z) = y).
