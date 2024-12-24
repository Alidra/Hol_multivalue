Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1504864 : forall x : real, forall y : real, (real_add (real_sub x y) y) = x.
