Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2292408 : forall x : int, forall y : int, (real_of_int (int_max x y)) = (real_max (real_of_int x) (real_of_int y)).