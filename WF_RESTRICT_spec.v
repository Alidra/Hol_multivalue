Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem359703 : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall P : A -> Prop, (@WF A lt2) -> @WF A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (lt2 x y))).
