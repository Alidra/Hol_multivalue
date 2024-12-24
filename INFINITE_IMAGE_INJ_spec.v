Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3630638 : forall {A B : Type'}, forall f : A -> B, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) -> forall s : A -> Prop, (@INFINITE A s) -> @INFINITE B (@IMAGE A B f s).
