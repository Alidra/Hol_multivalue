Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4475749 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall u : (prod K A) -> Prop, (@SUBSET (prod K A) u (@disjoint_union A K k s)) = (exists t : K -> A -> Prop, (u = (@disjoint_union A K k t)) /\ (forall i : K, (@IN K i k) -> @SUBSET A (t i) (s i))).
