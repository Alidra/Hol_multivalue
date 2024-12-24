Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310379 : forall x : int, forall y : int, forall z : int, (int_mul (int_sub x y) z) = (int_sub (int_mul x z) (int_mul y z)).
