Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306398 : forall x : int, forall y : int, ((int_neg x) = y) = (x = (int_neg y)).