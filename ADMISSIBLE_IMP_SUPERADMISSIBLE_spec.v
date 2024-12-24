Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8239494 : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> B, (@admissible A B A B P lt2 p s t) -> @superadmissible A B P lt2 p s t.
