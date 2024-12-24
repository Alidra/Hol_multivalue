Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1517224 : forall x : real, forall y : real, forall z : real, (real_le (real_sub x y) z) = (real_le x (real_add z y)).
