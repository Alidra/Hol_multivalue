Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3320763 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@INTER A (@DELETE A s x) t) = (@DELETE A (@INTER A s t) x).
