Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3379794 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@SUBSET A t s)) -> (@IMAGE A B f (@DIFF A s t)) = (@DIFF B (@IMAGE A B f s) (@IMAGE A B f t)).
