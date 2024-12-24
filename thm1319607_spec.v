Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1319607 : forall x : hreal, forall y : hreal, hreal_le x (hreal_add x y).
