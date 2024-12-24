Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4380688 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall s' : A -> Prop, forall t' : B -> Prop, (@DISJOINT (prod A B) (@CROSS B A s t) (@CROSS B A s' t')) = ((@DISJOINT A s s') \/ (@DISJOINT B t t')).
