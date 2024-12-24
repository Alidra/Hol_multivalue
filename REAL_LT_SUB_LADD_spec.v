Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1515170 : forall x : real, forall y : real, forall z : real, (real_lt x (real_sub y z)) = (real_lt (real_add x z) y).
