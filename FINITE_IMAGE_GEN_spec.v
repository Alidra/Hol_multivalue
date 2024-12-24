Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3624673 : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, forall s : A -> Prop, forall t : B -> Prop, ((@SUBSET B (@IMAGE A B f s) t) /\ ((@FINITE B t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> (g x) = (g y)))) -> @FINITE C (@IMAGE A C g s).
