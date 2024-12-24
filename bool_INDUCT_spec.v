Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem15306 : forall P : Prop -> Prop, ((P False) /\ (P True)) -> forall x : Prop, P x.
