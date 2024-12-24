Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5042894 : forall {A B : Type'}, forall f : A -> B, (forall t : B -> Prop, exists s : A -> Prop, (@IMAGE A B f s) = t) = (forall y : B, exists x : A, (f x) = y).
