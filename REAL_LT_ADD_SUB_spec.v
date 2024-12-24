Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1513116 : forall x : real, forall y : real, forall z : real, (real_lt (real_add x y) z) = (real_lt x (real_sub z y)).
