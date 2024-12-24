Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5096180 : forall {A B : Type'} (n : nat), forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, forall g : B -> A, ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ ((forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)) /\ (@HAS_SIZE A s n))) -> @HAS_SIZE B t n.
