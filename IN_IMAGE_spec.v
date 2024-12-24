Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3206070 : forall {A B : Type'}, forall y : B, forall s : A -> Prop, forall f : A -> B, (@IN B y (@IMAGE A B f s)) = (exists x : A, (y = (f x)) /\ (@IN A x s)).
