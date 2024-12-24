Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299942 : forall (x : int) (y : int), (fun y' : int => (real_le (real_of_int x) (real_of_int y')) = (int_le x y')) y.
