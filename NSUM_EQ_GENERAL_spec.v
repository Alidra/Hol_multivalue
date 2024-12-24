Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7018205 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> nat, forall g : B -> nat, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@nsum A s f) = (@nsum B t g).
