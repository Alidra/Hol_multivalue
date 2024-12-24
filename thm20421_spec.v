Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20421 : forall (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True), (((b = False) -> x = x0) /\ ((b = True) -> x = x1)) -> x = ((b /\ x1) \/ ((~ b) /\ x0)).
