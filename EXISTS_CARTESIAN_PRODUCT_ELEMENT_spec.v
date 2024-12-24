Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4455638 : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (exists z : K -> A, (@IN (K -> A) z (@cartesian_product A K k s)) /\ (forall i : K, (@IN K i k) -> P i (z i))) = (forall i : K, (@IN K i k) -> exists x : A, (@IN A x (s i)) /\ (P i x)).
