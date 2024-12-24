Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4390547 : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> B, (@SUBSET A s t) -> (@RESTRICTION A B s (@RESTRICTION A B t f)) = (@RESTRICTION A B s f).
