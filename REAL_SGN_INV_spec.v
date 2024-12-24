Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1734683 : forall x : real, (real_sgn (real_inv x)) = (real_sgn x).
