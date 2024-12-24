Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3382023 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall a : A, (forall x : A, ((@IN A x s) /\ ((f x) = (f a))) -> x = a) -> (@IMAGE A B f (@DELETE A s a)) = (@DELETE B (@IMAGE A B f s) (f a)).
