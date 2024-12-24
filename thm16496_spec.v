Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16496 : forall (t : Prop), ((t /\ False) = False) /\ ((t /\ t) = t).
