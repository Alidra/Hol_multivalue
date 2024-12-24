Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302158 : forall x : int, forall y : int, forall z : int, ((int_le x y) /\ (int_lt y z)) -> int_lt x z.
