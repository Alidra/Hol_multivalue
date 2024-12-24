Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4387092 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, forall y : B, ((@IN A x s) /\ ((f x) = y)) -> (@RESTRICTION A B s f x) = y.
