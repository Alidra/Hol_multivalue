Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1502113 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_le w x) /\ (real_le y z)) -> real_le (real_add w y) (real_add x z).
