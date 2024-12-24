Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3255345 : forall {A : Type'}, forall s : A -> Prop, (@INTER A s s) = s.
