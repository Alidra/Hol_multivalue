Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841579 : forall (x : int) (y : int), (fun y' : int => (real_of_int (int_mul x y')) = (real_mul (real_of_int x) (real_of_int y'))) y.
