Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2292270 : forall x : int, forall y : int, (int_max x y) = (int_of_real (real_max (real_of_int x) (real_of_int y))).
