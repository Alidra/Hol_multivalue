Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299700 : forall x : int, forall y : int, (real_le (real_of_int x) (real_of_int y)) = (int_le x y).