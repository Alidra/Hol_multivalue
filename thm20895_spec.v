Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20895 : forall (a : Prop) (b : Prop), (~ (a \/ b)) = ((~ a) /\ (~ b)).
