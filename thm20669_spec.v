Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20669 : forall (p : Prop) (q : Prop), ((p \/ p) = p) /\ ((p \/ (p \/ q)) = (p \/ q)).
