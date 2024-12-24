Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301623 : forall x : int, forall y : int, (x = y) -> int_le x y.
