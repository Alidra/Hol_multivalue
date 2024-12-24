Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318569 : forall (x : int) (y : int), ((fun y' : int => (int_le x y') = (real_le (real_of_int x) (real_of_int y'))) y) = ((int_le x y) = (real_le (real_of_int x) (real_of_int y))).
