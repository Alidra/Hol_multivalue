Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem11203 : forall (P : Prop -> Prop), (exists b : Prop, P b) = ((P True) \/ (P False)).
