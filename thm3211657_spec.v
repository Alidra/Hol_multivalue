Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211657 : forall {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop), ((fun f' : A -> B => (@IN B y (@IMAGE A B f' s)) = (exists x : A, (y = (f' x)) /\ (@IN A x s))) f) = ((@IN B y (@IMAGE A B f s)) = (exists x : A, (y = (f x)) /\ (@IN A x s))).
