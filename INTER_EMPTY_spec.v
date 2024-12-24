Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3258370 : forall {A : Type'}, (forall s : A -> Prop, (@INTER A (@EMPTY A) s) = (@EMPTY A)) /\ (forall s : A -> Prop, (@INTER A s (@EMPTY A)) = (@EMPTY A)).
