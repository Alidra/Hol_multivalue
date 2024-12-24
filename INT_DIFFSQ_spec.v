Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301438 : forall x : int, forall y : int, (int_mul (int_add x y) (int_sub x y)) = (int_sub (int_mul x x) (int_mul y y)).
