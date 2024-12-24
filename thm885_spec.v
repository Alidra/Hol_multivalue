Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem885 : forall (p : Prop) (q : Prop) (r : Prop), (((p /\ q) -> r) -> p -> q -> r) /\ ((p -> q -> r) -> (p /\ q) -> r).
