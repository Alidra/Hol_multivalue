Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301272 : forall x : int, forall y : int, (int_sub (int_add x y) x) = y.
