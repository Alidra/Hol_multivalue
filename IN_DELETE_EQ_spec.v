Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3306761 : forall {A : Type'}, forall s : A -> Prop, forall x : A, forall x' : A, ((@IN A x s) = (@IN A x' s)) = ((@IN A x (@DELETE A s x')) = (@IN A x' (@DELETE A s x))).
