Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem70827 : forall x : ind, ~ ((IND_SUC x) = IND_0).
