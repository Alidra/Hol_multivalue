Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3307760 : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@DELETE A (@DELETE A s x) x) = (@DELETE A s x).
