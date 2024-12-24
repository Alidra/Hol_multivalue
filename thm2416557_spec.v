Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416557 : forall (a : int) (b : int) (c : int), (int_add (int_add a b) c) = (int_add a (int_add b c)).
