Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299931 : forall (x : int) (y : int), ((fun y' : int => (real_ge (real_of_int x) (real_of_int y')) = (int_ge x y')) y) = ((real_ge (real_of_int x) (real_of_int y)) = (int_ge x y)).
