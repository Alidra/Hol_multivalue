Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1947279 : forall x : real, forall y : real, (sqrt (real_mul x y)) = (real_mul (sqrt x) (sqrt y)).
