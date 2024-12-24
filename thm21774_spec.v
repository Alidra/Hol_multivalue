Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21774 : forall (t : Prop), ((t -> t) = True) /\ ((t -> False) = (~ t)).
