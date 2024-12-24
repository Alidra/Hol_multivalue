Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299924 : forall (x : int) (y : int), (fun y' : int => (real_gt (real_of_int x) (real_of_int y')) = (int_gt x y')) y.
