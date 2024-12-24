Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1526141 : forall x : real, forall y : real, (real_lt (real_neg x) (real_neg y)) = (real_lt y x).
