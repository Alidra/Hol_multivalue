Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4405001 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall f : K -> A, (@IN (K -> A) (@RESTRICTION K A k f) (@cartesian_product A K k s)) = (forall i : K, (@IN K i k) -> @IN A (f i) (s i)).
