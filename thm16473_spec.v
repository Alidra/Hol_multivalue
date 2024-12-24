Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16473 : forall (t : Prop), ((False -> t) = True) /\ (((t -> t) = True) /\ ((t -> False) = (~ t))).
