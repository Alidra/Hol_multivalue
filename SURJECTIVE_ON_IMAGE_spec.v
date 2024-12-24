Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5042707 : forall {A B : Type'}, forall f : A -> B, forall u : A -> Prop, forall v : B -> Prop, (forall t : B -> Prop, (@SUBSET B t v) -> exists s : A -> Prop, (@SUBSET A s u) /\ ((@IMAGE A B f s) = t)) = (forall y : B, (@IN B y v) -> exists x : A, (@IN A x u) /\ ((f x) = y)).
