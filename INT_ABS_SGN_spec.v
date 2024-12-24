Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300613 : forall x : int, (int_abs (int_sgn x)) = (int_sgn (int_abs x)).
