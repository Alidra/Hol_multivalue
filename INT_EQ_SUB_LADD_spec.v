Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301939 : forall x : int, forall y : int, forall z : int, (x = (int_sub y z)) = ((int_add x z) = y).
