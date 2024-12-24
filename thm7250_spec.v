Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7250 : forall (A : Prop) (C : Prop) (B : Prop) (D : Prop), ((B -> A) /\ (C -> D)) -> (A -> C) -> B -> D.
