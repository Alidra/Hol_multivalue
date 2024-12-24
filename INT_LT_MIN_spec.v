Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2304344 : forall x : int, forall y : int, forall z : int, (int_lt z (int_min x y)) = ((int_lt z x) /\ (int_lt z y)).
