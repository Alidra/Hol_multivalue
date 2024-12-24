Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3816218 : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> ((@ITSET B A f (@EMPTY A) b) = b) /\ (forall x : A, forall s : A -> Prop, (@FINITE A s) -> (@ITSET B A f (@INSERT A x s) b) = (@COND B (@IN A x s) (@ITSET B A f s b) (f x (@ITSET B A f s b)))).
