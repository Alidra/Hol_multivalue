Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21487 : forall (b : Prop) (a : Prop) (h1 : a = False), (a -> b) = ((~ a) \/ b).