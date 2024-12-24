Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16464 : forall (t : Prop), ((False = t) = (~ t)) /\ ((t = False) = (~ t)).
