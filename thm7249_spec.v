Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7249 : forall (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : (B -> A) /\ (C -> D)), (A -> C) -> B -> D.
