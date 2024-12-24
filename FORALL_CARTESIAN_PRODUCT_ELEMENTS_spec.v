Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4452398 : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (forall z : K -> A, forall i : K, ((@IN (K -> A) z (@cartesian_product A K k s)) /\ (@IN K i k)) -> P i (z i)) = (((@cartesian_product A K k s) = (@EMPTY (K -> A))) \/ (forall i : K, forall x : A, ((@IN K i k) /\ (@IN A x (s i))) -> P i x)).
