Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2267726 : forall (a : int), (int_of_real (real_of_int a)) = a.
