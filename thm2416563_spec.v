Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416563 : forall (c : int) (a : int), (int_add a c) = (int_add c a).
