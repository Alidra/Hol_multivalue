Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302441 : forall x : int, forall y : int, forall z : int, (int_le y z) -> int_le (int_add x y) (int_add x z).
