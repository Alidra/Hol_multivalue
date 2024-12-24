Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3272928 : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@IN A x s) = (exists t : A -> Prop, (s = (@INSERT A x t)) /\ (~ (@IN A x t))).
