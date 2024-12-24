Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3743381 : forall {A : Type'}, forall R : A -> A -> Prop, forall s : A -> Prop, ((@FINITE A s) /\ ((forall x : A, ~ (R x x)) /\ ((forall x : A, forall y : A, forall z : A, ((R x y) /\ (R y z)) -> R x z) /\ (forall x : A, (@IN A x s) -> exists y : A, (@IN A y s) /\ (R x y))))) -> s = (@EMPTY A).
