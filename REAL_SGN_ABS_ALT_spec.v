Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1719699 : forall x : real, (real_mul (real_sgn x) x) = (real_abs x).
