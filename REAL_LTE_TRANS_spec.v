Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1370312 : forall x : real, forall y : real, forall z : real, ((real_lt x y) /\ (real_le y z)) -> real_lt x z.
