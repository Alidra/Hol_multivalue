Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301866 : forall x : int, forall y : int, (x = y) = (((int_sgn x) = (int_sgn y)) /\ ((int_abs x) = (int_abs y))).
