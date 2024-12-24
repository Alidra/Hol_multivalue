Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3255901 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@INTER A s t) = (@INTER A t s).
