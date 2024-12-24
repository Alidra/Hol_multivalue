Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416559 : forall (c : int) (a : int) (d : int), (int_add a (int_add c d)) = (int_add c (int_add a d)).
