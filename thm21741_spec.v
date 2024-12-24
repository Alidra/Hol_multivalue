Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21741 : forall (t : Prop), ((t = True) = t) /\ (((False = t) = (~ t)) /\ ((t = False) = (~ t))).
