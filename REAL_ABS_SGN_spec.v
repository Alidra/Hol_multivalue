Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1733749 : forall x : real, (real_abs (real_sgn x)) = (real_sgn (real_abs x)).
