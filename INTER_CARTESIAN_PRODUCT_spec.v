Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4432366 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@INTER (K -> A) (@cartesian_product A K k s) (@cartesian_product A K k t)) = (@cartesian_product A K k (fun i : K => @INTER A (s i) (t i))).
