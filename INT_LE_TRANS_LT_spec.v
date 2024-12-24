Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2336267 : forall x : int, forall y : int, (int_le x y) = (forall z : int, (int_lt y z) -> int_lt x z).
