Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1995414 : forall x : real, forall y : real, (real_le x y) = (forall z : real, (real_lt y z) -> real_lt x z).
