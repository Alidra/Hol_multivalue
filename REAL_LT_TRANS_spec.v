Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1372268 : forall x : real, forall y : real, forall z : real, ((real_lt x y) /\ (real_lt y z)) -> real_lt x z.
