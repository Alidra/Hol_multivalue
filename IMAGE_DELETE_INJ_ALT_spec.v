Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3384547 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall a : A, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@IN A a s)) -> (@IMAGE A B f (@DELETE A s a)) = (@DELETE B (@IMAGE A B f s) (f a)).
