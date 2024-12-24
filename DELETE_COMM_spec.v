Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3308927 : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@DELETE A (@DELETE A s x) y) = (@DELETE A (@DELETE A s y) x).
