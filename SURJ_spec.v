Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3201623 : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, forall f : A -> B, (@SURJ A B f s t) = ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : B, (@IN B x t) -> exists y : A, (@IN A y s) /\ ((f y) = x))).
