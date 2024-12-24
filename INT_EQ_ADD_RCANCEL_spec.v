Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301576 : forall x : int, forall y : int, forall z : int, ((int_add x z) = (int_add y z)) = (x = y).
