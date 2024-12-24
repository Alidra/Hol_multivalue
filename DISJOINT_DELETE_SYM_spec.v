Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3322076 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@DISJOINT A (@DELETE A s x) t) = (@DISJOINT A (@DELETE A t x) s).
