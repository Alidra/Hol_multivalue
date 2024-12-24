Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem794 : forall (q : Prop) (p : Prop) (r : Prop), (((p \/ (q \/ r)) -> q \/ (p \/ r)) /\ ((q \/ (p \/ r)) -> p \/ (q \/ r))) = ((p \/ (q \/ r)) = (q \/ (p \/ r))).
