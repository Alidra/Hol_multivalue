Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21433 : forall (b : Prop) (a : Prop) (h1 : a = False), ((False -> b) = ((~ False) \/ b)) = ((a -> b) = ((~ a) \/ b)).