Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1509403 : forall x : real, forall y : real, (real_lt x y) -> ~ (x = y).