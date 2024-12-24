Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1487294 : forall x : real, forall y : real, forall z : real, (real_lt y z) -> real_lt (real_add x y) (real_add x z).
