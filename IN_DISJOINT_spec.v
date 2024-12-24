Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3264346 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A s t) = (~ (exists x : A, (@IN A x s) /\ (@IN A x t))).
