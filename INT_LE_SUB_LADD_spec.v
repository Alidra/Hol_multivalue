Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303371 : forall x : int, forall y : int, forall z : int, (int_le x (int_sub y z)) = (int_le (int_add x z) y).
