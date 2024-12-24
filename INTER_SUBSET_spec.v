Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3256723 : forall {A : Type'}, (forall s : A -> Prop, forall t : A -> Prop, @SUBSET A (@INTER A s t) s) /\ (forall s : A -> Prop, forall t : A -> Prop, @SUBSET A (@INTER A t s) s).
