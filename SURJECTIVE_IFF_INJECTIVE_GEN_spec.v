Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4944739 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, ((@FINITE A s) /\ ((@FINITE B t) /\ (((@CARD A s) = (@CARD B t)) /\ (@SUBSET B (@IMAGE A B f s) t)))) -> (forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
