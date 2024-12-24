Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5092652 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall a : A, forall b : B, ((@FINITE A s) /\ ((@FINITE B t) /\ (((@CARD A s) = (@CARD B t)) /\ ((@IN A a s) /\ (@IN B b t))))) -> exists f : A -> B, exists g : B -> A, ((f a) = b) /\ (((g b) = a) /\ ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)))).
