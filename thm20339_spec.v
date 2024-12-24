Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20339 : forall (x : Prop) (x1 : Prop) (x0 : Prop), (((True = False) -> x = x0) /\ ((True = True) -> x = x1)) -> x = ((True /\ x1) \/ ((~ True) /\ x0)).
