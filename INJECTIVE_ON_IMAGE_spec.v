Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5037470 : forall {A B : Type'}, forall f : A -> B, forall u : A -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@SUBSET A s u) /\ ((@SUBSET A t u) /\ ((@IMAGE A B f s) = (@IMAGE A B f t)))) -> s = t) = (forall x : A, forall y : A, ((@IN A x u) /\ ((@IN A y u) /\ ((f x) = (f y)))) -> x = y).
