Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3641047 : forall {A B : Type'}, forall f : A -> B, forall s : B -> Prop, forall t : A -> Prop, (@SUBSET B s (@IMAGE A B f t)) = (exists u : A -> Prop, (@SUBSET A u t) /\ ((forall x : A, forall y : A, ((@IN A x u) /\ (@IN A y u)) -> ((f x) = (f y)) = (x = y)) /\ (s = (@IMAGE A B f u)))).
