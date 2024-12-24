Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1273055 : forall x : nadd, forall y : nadd, (nadd_le x y) \/ (nadd_le y x).
