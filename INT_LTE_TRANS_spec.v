Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303637 : forall x : int, forall y : int, forall z : int, ((int_lt x y) /\ (int_le y z)) -> int_lt x z.
