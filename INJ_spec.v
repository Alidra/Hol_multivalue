Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3200579 : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, forall f : A -> B, (@INJ A B f s t) = ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
