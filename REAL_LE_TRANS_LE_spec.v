Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1989784 : forall x : real, forall y : real, (real_le x y) = (forall z : real, (real_le y z) -> real_le x z).
