Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211656 : forall {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B), (fun f' : A -> B => (@IN B y (@IMAGE A B f' s)) = (exists x : A, (y = (f' x)) /\ (@IN A x s))) f.
