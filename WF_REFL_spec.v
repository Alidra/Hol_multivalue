Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem369021 : forall {A : Type'} (lt2 : A -> A -> Prop), forall x : A, (@WF A lt2) -> ~ (lt2 x x).
