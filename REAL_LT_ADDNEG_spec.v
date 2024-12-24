Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1503294 : forall x : real, forall y : real, forall z : real, (real_lt y (real_add x (real_neg z))) = (real_lt (real_add y z) x).
