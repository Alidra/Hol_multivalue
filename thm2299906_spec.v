Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299906 : forall (x : int) (y : int), (fun y' : int => (real_mul (real_of_int x) (real_of_int y')) = (real_of_int (int_mul x y'))) y.
