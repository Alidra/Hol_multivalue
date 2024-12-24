Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4491919 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, ((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (forall i : K, (@IN K i k) -> (s i) = (@EMPTY A)).
