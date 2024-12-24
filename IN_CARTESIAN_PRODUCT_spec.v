Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4399593 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, (@IN (K -> A) x (@cartesian_product A K k s)) = ((@EXTENSIONAL K A k x) /\ (forall i : K, (@IN K i k) -> @IN A (x i) (s i))).
