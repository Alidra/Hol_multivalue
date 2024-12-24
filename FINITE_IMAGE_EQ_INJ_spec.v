Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3734144 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@FINITE B (@IMAGE A B f s)) = (exists t : A -> Prop, (@FINITE A t) /\ ((@SUBSET A t s) /\ (((@IMAGE A B f s) = (@IMAGE A B f t)) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y))))).
