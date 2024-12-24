Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2520091 : forall x : int, forall y : int, (rem x (int_abs y)) = (rem x y).
