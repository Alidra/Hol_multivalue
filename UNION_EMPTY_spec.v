Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3235853 : forall {A : Type'}, (forall s : A -> Prop, (@UNION A (@EMPTY A) s) = s) /\ (forall s : A -> Prop, (@UNION A s (@EMPTY A)) = s).
