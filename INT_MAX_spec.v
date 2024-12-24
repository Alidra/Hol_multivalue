Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2323496 : forall x : int, forall y : int, (int_max x y) = (@COND int (int_le x y) y x).
