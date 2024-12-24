Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303886 : forall x : int, forall y : int, forall z : int, (int_lt (int_add x (int_neg y)) z) = (int_lt x (int_add z y)).
