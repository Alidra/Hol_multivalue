Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1574873 : forall x : real, forall y : real, forall z : real, (real_min x (real_min y z)) = (real_min (real_min x y) z).
