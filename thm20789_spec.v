Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20789 : forall (a : Prop) (b : Prop), ((~ (a \/ b)) = ((~ a) /\ (~ b))) = ((~ (a \/ b)) = ((~ a) /\ (~ b))).
