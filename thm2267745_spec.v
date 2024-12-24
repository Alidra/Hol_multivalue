Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2267745 : forall (a : int), ((fun a' : int => (int_of_real (real_of_int a')) = a') a) = ((int_of_real (real_of_int a)) = a).
