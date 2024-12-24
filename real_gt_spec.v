Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1342768 : forall y : real, forall x : real, (real_gt x y) = (real_lt y x).
