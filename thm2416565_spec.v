Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416565 : forall (a : int) (c : int) (d : int), (int_add a (int_add c d)) = (int_add (int_add a c) d).
