Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4469801 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, ((@disjoint_union A K k s) = (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> (s i) = (t i)).
