Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4429904 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = ((((@cartesian_product A K k s) = (@EMPTY (K -> A))) /\ ((@cartesian_product A K k t) = (@EMPTY (K -> A)))) \/ (forall i : K, (@IN K i k) -> (s i) = (t i))).
