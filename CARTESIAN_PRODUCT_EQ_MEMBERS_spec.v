Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4409647 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, forall y : K -> A, ((@IN (K -> A) x (@cartesian_product A K k s)) /\ ((@IN (K -> A) y (@cartesian_product A K k s)) /\ (forall i : K, (@IN K i k) -> (x i) = (y i)))) -> x = y.
