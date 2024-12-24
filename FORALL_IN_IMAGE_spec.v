Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3386920 : forall {_87967 _87968 : Type'} (P : _87967 -> Prop), forall f : _87968 -> _87967, forall s : _87968 -> Prop, (forall y : _87967, (@IN _87967 y (@IMAGE _87968 _87967 f s)) -> P y) = (forall x : _87968, (@IN _87968 x s) -> P (f x)).
