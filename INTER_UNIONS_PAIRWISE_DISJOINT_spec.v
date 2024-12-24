Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4833713 : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (@pairwise (A -> Prop) (@DISJOINT A) (@UNION (A -> Prop) s t)) -> (@INTER A (@UNIONS A s) (@UNIONS A t)) = (@UNIONS A (@INTER (A -> Prop) s t)).
