Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318515 : forall (x : int), ((fun x' : int => (real_of_int (int_abs x')) = (real_abs (real_of_int x'))) x) = ((real_of_int (int_abs x)) = (real_abs (real_of_int x))).