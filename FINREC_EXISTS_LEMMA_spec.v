Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3808349 : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, forall s : A -> Prop, (@FINITE A s) -> exists a : B, exists n : nat, @FINREC A B f b s a n.
