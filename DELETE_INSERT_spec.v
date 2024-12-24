Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3318884 : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@DELETE A (@INSERT A x s) y) = (@COND (A -> Prop) (x = y) (@DELETE A s y) (@INSERT A x (@DELETE A s y))).
