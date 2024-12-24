Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4963588 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, ((@FINITE A s) /\ (((@CARD A s) = (@CARD B t)) /\ ((@IMAGE A B f s) = t))) -> forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y.
