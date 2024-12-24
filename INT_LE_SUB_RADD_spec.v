Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303406 : forall x : int, forall y : int, forall z : int, (int_le (int_sub x y) z) = (int_le x (int_add z y)).
