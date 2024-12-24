Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3797397 : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> forall n : nat, forall s : A -> Prop, forall z : B, (@FINREC A B f b s z (S n)) -> forall x : A, (@IN A x s) -> exists w : B, (@FINREC A B f b (@DELETE A s x) w n) /\ (z = (f x w)).
