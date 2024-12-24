Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3266941 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@DISJOINT A (@UNION A s t) u) = ((@DISJOINT A s u) /\ (@DISJOINT A t u)).
