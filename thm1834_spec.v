Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1834 : forall (t : Prop), ((t \/ False) = t) /\ ((t \/ t) = t).