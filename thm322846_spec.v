Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem322846 : forall {A B : Type'} (H : (A -> B) -> A -> B) (lt2 : A -> A -> Prop), exists R : A -> B -> Prop, (forall f : A -> B, forall x : A, (forall z : A, (lt2 z x) -> R z (f z)) -> R x (H f x)) /\ ((forall R' : A -> B -> Prop, (forall f : A -> B, forall x : A, (forall z : A, (lt2 z x) -> R' z (f z)) -> R' x (H f x)) -> forall a0 : A, forall a1 : B, (R a0 a1) -> R' a0 a1) /\ (forall a0 : A, forall a1 : B, (R a0 a1) = (exists f : A -> B, (a1 = (H f a0)) /\ (forall z : A, (lt2 z a0) -> R z (f z))))).
