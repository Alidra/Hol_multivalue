Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1992599 : forall x : real, forall y : real, (real_le x y) = (forall z : real, (real_lt y z) -> real_le x z).
