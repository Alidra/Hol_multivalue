Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305281 : forall x : int, forall y : int, forall z : int, (int_max x (int_max y z)) = (int_max (int_max x y) z).
