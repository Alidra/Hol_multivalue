Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3585065 : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (forall x : A, P (f x)) = (forall y : B, P y)).
