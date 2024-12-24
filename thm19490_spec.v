Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem19490 : forall (b : Prop) (a : Prop) (c : Prop), (a \/ (b /\ c)) = ((a \/ b) /\ (a \/ c)).
