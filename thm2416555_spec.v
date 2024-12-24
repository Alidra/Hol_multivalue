Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416555 : forall (a : int) (c : int) (b : int) (d : int), (int_add (int_add a b) (int_add c d)) = (int_add (int_add a c) (int_add b d)).
