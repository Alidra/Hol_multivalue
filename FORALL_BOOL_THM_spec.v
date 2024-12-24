Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem11006 : forall (P : Prop -> Prop), (forall b : Prop, P b) = ((P True) /\ (P False)).
