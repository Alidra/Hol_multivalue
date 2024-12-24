Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5073217 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ ((@FINITE B t) /\ ((@CARD A s) = (@CARD B t)))) -> exists f : A -> B, exists g : B -> A, (forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)).
