Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1735073 : forall x : real, forall y : real, (real_sgn (real_div x y)) = (real_div (real_sgn x) (real_sgn y)).
