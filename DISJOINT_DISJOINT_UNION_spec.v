Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4492048 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@DISJOINT (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> @DISJOINT A (s i) (t i)).
