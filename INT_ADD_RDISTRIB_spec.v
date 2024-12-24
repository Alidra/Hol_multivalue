Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301200 : forall x : int, forall y : int, forall z : int, (int_mul (int_add x y) z) = (int_add (int_mul x z) (int_mul y z)).
