Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7178400 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> real, forall g : B -> real, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@sum A s f) = (@sum B t g).
