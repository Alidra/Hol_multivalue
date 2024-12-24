Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301067 : forall x : int, forall y : int, forall z : int, (int_add x (int_add y z)) = (int_add (int_add x y) z).
