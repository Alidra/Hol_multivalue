Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299728 : forall x : int, forall y : int, (real_ge (real_of_int x) (real_of_int y)) = (int_ge x y).
