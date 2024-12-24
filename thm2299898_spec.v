Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299898 : forall (x : int) (y : int), ((fun y' : int => (real_sub (real_of_int x) (real_of_int y')) = (real_of_int (int_sub x y'))) y) = ((real_sub (real_of_int x) (real_of_int y)) = (real_of_int (int_sub x y))).
