Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7130 : forall (A : Prop) (C : Prop) (B : Prop) (D : Prop), ((A -> B) /\ (C -> D)) -> (A \/ C) -> B \/ D.
