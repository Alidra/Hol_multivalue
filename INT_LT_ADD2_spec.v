Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303771 : forall w : int, forall x : int, forall y : int, forall z : int, ((int_lt w x) /\ (int_lt y z)) -> int_lt (int_add w y) (int_add x z).