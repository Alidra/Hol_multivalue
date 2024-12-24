Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem361737 : forall {A B : Type'}, forall lt2 : B -> B -> Prop, forall m : A -> B, (@WF B lt2) -> @WF A (fun x : A => fun x' : A => lt2 (m x) (m x')).
