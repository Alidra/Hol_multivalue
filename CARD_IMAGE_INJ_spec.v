Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3996358 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@FINITE A s)) -> (@CARD B (@IMAGE A B f s)) = (@CARD A s).
