Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301108 : forall x : int, forall y : int, forall z : int, (int_mul x (int_add y z)) = (int_add (int_mul x y) (int_mul x z)).
