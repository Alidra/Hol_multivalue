Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5037682 : forall {A B : Type'}, forall f : A -> B, (forall s : A -> Prop, forall t : A -> Prop, ((@IMAGE A B f s) = (@IMAGE A B f t)) -> s = t) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
