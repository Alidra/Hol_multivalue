Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305041 : forall x : int, forall y : int, forall z : int, (int_lt (int_sub x y) z) = (int_lt x (int_add z y)).