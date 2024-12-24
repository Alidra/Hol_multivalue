Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1947445 : forall x : real, forall y : real, (sqrt (real_div x y)) = (real_div (sqrt x) (sqrt y)).
