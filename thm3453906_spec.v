Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3453906 : forall {A : Type'} (s : A -> Prop) (t : A -> Prop), ((fun t' : A -> Prop => (s = t') = (forall x : A, (@IN A x s) = (@IN A x t'))) t) = ((s = t) = (forall x : A, (@IN A x s) = (@IN A x t))).
