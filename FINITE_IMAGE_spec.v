Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3615104 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@FINITE A s) -> @FINITE B (@IMAGE A B f s).
