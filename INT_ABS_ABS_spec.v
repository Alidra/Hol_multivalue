Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300012 : forall x : int, (int_abs (int_abs x)) = (int_abs x).
