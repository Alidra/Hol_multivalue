Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303450 : forall x : int, forall y : int, forall z : int, ((int_le x y) /\ (int_le y z)) -> int_le x z.
