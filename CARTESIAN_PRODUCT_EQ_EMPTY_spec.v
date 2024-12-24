Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4408929 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (exists i : K, (@IN K i k) /\ ((s i) = (@EMPTY A))).
