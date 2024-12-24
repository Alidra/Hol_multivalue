Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301780 : forall x : int, forall y : int, ((int_neg x) = (int_neg y)) = (x = y).
