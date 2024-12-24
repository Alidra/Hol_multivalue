Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1512089 : forall x : real, forall y : real, (real_sub (real_sub x y) x) = (real_neg y).
