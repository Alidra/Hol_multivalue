Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem644 : forall (p : Prop) (q : Prop), (((p /\ (p /\ q)) -> p /\ q) /\ ((p /\ q) -> p /\ (p /\ q))) = ((p /\ (p /\ q)) = (p /\ q)).