Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1501615 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_lt w x) /\ (real_lt y z)) -> real_lt (real_add w y) (real_add x z).
