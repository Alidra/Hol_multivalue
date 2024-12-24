Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1733933 : forall x : real, (real_sgn x) = (real_div x (real_abs x)).
