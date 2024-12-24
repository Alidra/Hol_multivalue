Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4392828 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (@SUBSET A s t) -> (@IMAGE A B (@RESTRICTION A B t f) s) = (@IMAGE A B f s).
