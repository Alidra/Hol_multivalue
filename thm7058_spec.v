Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7058 : forall (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : (A -> B) /\ (C -> D)), (A /\ C) -> B /\ D.
