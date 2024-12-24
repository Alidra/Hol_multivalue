Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305765 : forall x : int, forall y : int, (int_le (int_min x y) x) /\ (int_le (int_min x y) y).
