Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4829792 : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, ((@pairwise (A -> Prop) (@DISJOINT A) s) /\ (@SUBSET (A -> Prop) t s)) -> (@DIFF A (@UNIONS A s) (@UNIONS A t)) = (@UNIONS A (@DIFF (A -> Prop) s t)).
