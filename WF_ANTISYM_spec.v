Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem368295 : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall x : A, forall y : A, (@WF A lt2) -> ~ ((lt2 x y) /\ (lt2 y x)).
