Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5029861 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ ((@FINITE B t) /\ (Peano.le (@CARD A s) (@CARD B t)))) -> exists f : A -> B, (@SUBSET B (@IMAGE A B f s) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
