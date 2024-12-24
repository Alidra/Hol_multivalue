Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem554 : forall (p : Prop) (q : Prop), ((p /\ q) -> q /\ p) /\ ((q /\ p) -> p /\ q).
