Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem805 : forall (p : Prop), (((p \/ p) -> p) /\ (p -> p \/ p)) = ((p \/ p) = p).