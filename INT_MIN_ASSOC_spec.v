Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305627 : forall x : int, forall y : int, forall z : int, (int_min x (int_min y z)) = (int_min (int_min x y) z).
