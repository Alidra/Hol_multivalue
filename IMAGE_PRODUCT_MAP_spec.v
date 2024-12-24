Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4463342 : forall {A B K : Type'}, forall f : K -> A -> B, forall k : K -> Prop, forall s : K -> A -> Prop, (@IMAGE (K -> A) (K -> B) (@product_map A B K k f) (@cartesian_product A K k s)) = (@cartesian_product B K k (fun i : K => @IMAGE A B (f i) (s i))).
