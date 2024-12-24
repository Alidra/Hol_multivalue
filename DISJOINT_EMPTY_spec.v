Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3265352 : forall {A : Type'}, forall s : A -> Prop, (@DISJOINT A (@EMPTY A) s) /\ (@DISJOINT A s (@EMPTY A)).
