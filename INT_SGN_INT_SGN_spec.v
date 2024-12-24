Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309854 : forall x : int, (int_sgn (int_sgn x)) = (int_sgn x).
