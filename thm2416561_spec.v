Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416561 : forall (a : int) (c : int) (b : int), (int_add (int_add a b) c) = (int_add (int_add a c) b).
