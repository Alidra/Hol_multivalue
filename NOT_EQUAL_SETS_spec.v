Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3213431 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (~ (s = t)) = (exists x : A, (@IN A x t) = (~ (@IN A x s))).
