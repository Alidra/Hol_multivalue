Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3576800 : forall {A B : Type'}, forall f : A -> B, ((forall x : A, forall y : A, ((f x) = (f y)) -> x = y) /\ (forall y : B, exists x : A, (f x) = y)) = (exists g : B -> A, (forall y : B, (f (g y)) = y) /\ (forall x : A, (g (f x)) = x)).
