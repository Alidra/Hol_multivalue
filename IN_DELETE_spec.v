Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3205803 : forall {A : Type'}, forall s : A -> Prop, forall x : A, forall y : A, (@IN A x (@DELETE A s y)) = ((@IN A x s) /\ (~ (x = y))).