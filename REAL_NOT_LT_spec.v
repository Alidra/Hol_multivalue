Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1376537 : forall x : real, forall y : real, (~ (real_lt x y)) = (real_le y x).
