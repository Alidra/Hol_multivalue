Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3258568 : forall {A : Type'}, (forall s : A -> Prop, (@INTER A (@UNIV A) s) = s) /\ (forall s : A -> Prop, (@INTER A s (@UNIV A)) = s).
