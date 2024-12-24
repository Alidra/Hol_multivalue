Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305379 : forall x : int, forall y : int, (int_le x (int_max x y)) /\ (int_le y (int_max x y)).
