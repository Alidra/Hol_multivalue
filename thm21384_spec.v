Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21384 : forall {A : Type'} (x : A) (y : A) (z : A), (x = x) /\ ((~ (x = y)) \/ ((~ (x = z)) \/ (y = z))).