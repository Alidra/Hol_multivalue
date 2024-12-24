Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1516197 : forall x : real, forall y : real, forall z : real, (real_le x (real_sub y z)) = (real_le (real_add x z) y).
