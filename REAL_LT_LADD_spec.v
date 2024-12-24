Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1492692 : forall x : real, forall y : real, forall z : real, (real_lt (real_add x y) (real_add x z)) = (real_lt y z).
