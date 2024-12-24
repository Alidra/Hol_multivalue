Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1507870 : forall x : real, forall y : real, (real_sub (real_add x y) x) = y.
