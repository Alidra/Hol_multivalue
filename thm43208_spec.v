Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem43208 : forall (B : Prop) (D : Prop) (A : Prop) (C : Prop), ((B -> A) /\ (B -> D -> C)) -> (B /\ D) -> A /\ C.
