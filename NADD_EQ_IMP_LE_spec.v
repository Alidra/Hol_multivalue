Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1279763 : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_le x y.
