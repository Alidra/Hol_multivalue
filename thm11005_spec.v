Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem11005 : forall (P : Prop -> Prop), (((forall b : Prop, P b) -> (P True) /\ (P False)) /\ (((P True) /\ (P False)) -> forall b : Prop, P b)) = ((forall b : Prop, P b) = ((P True) /\ (P False))).
