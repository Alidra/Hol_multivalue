Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2304723 : forall x : int, forall y : int, forall z : int, (int_lt (int_add x z) (int_add y z)) = (int_lt x y).
