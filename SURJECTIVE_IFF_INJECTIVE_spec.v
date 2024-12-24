Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4945027 : forall {A : Type'}, forall s : A -> Prop, forall f : A -> A, ((@FINITE A s) /\ (@SUBSET A (@IMAGE A A f s) s)) -> (forall y : A, (@IN A y s) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
