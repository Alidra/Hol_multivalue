Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3286086 : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A (@INSERT A x s) t) = ((@DISJOINT A s t) /\ (~ (@IN A x t))).
