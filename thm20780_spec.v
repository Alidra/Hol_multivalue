Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20780 : forall (a : Prop), True = ((~ (~ a)) = a).