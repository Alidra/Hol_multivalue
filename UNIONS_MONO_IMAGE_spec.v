Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3349929 : forall {_87171 _87182 : Type'} (f : _87171 -> _87182 -> Prop) (g : _87171 -> _87182 -> Prop) (s : _87171 -> Prop), (forall x : _87171, (@IN _87171 x s) -> @SUBSET _87182 (f x) (g x)) -> @SUBSET _87182 (@UNIONS _87182 (@IMAGE _87171 (_87182 -> Prop) f s)) (@UNIONS _87182 (@IMAGE _87171 (_87182 -> Prop) g s)).
