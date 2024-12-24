Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3197081 : forall {A : Type'}, forall s : A -> Prop, (@SING A s) = (exists x : A, s = (@INSERT A x (@EMPTY A))).
