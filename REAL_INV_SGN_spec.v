Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1772483 : forall x : real, (real_inv (real_sgn x)) = (real_sgn x).
