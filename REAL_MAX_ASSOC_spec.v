Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1573168 : forall x : real, forall y : real, forall z : real, (real_max x (real_max y z)) = (real_max (real_max x y) z).
