Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1522949 : forall x : real, forall y : real, forall z : real, ((real_sub x y) = z) = (x = (real_add z y)).
