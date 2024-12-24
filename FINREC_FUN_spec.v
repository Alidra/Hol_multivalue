Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3812781 : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> exists g : (A -> Prop) -> B, ((g (@EMPTY A)) = b) /\ (forall s : A -> Prop, forall x : A, ((@FINITE A s) /\ (@IN A x s)) -> (g s) = (f x (g (@DELETE A s x)))).
