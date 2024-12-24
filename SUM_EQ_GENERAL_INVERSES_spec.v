Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7178548 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> real, forall g : B -> real, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@sum A s f) = (@sum B t g).
