Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305957 : forall x : int, forall y : int, forall z : int, (int_mul x (int_mul y z)) = (int_mul (int_mul x y) z).
