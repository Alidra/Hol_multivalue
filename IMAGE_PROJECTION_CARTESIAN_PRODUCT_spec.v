Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4446959 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall i : K, (@IMAGE (K -> A) A (fun x : K -> A => x i) (@cartesian_product A K k s)) = (@COND (A -> Prop) ((@cartesian_product A K k s) = (@EMPTY (K -> A))) (@EMPTY A) (@COND (A -> Prop) (@IN K i k) (s i) (@INSERT A (@ARB A) (@EMPTY A)))).
