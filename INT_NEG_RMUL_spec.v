Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306696 : forall x : int, forall y : int, (int_neg (int_mul x y)) = (int_mul x (int_neg y)).