Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299949 : forall (x : int) (y : int), ((fun y' : int => ((real_of_int x) = (real_of_int y')) = (x = y')) y) = (((real_of_int x) = (real_of_int y)) = (x = y)).
