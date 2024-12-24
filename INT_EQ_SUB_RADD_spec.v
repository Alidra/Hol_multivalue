Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301974 : forall x : int, forall y : int, forall z : int, ((int_sub x y) = z) = (x = (int_add z y)).
