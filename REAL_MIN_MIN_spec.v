Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1557933 : forall x : real, forall y : real, (real_le (real_min x y) x) /\ (real_le (real_min x y) y).
