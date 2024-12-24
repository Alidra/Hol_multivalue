Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5070396 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ ((@FINITE B t) /\ ((@CARD A s) = (@CARD B t)))) -> exists f : A -> B, (forall x : A, (@IN A x s) -> @IN B (f x) t) /\ ((forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
