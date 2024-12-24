Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1844 : forall (t : Prop), ((False /\ t) = False) /\ (((t /\ False) = False) /\ ((t /\ t) = t)).
