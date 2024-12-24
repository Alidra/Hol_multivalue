Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1594900 : forall x : real, forall y : real, (real_abs (real_div x y)) = (real_div (real_abs x) (real_abs y)).
