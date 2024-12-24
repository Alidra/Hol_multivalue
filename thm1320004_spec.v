Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1320004 : forall x : hreal, forall y : hreal, (hreal_add x y) = (hreal_add y x).
