Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2293159 : forall x : int, forall y : int, (int_min x y) = (int_of_real (real_min (real_of_int x) (real_of_int y))).
