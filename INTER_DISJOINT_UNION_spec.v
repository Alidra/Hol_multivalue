Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4482970 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@INTER (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (@disjoint_union A K k (fun i : K => @INTER A (s i) (t i))).
