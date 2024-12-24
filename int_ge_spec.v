Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2270452 : forall x : int, forall y : int, (int_ge x y) = (real_ge (real_of_int x) (real_of_int y)).
