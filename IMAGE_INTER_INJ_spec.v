Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3373798 : forall {_87647 _87658 : Type'}, forall f : _87647 -> _87658, forall s : _87647 -> Prop, forall t : _87647 -> Prop, (forall x : _87647, forall y : _87647, ((f x) = (f y)) -> x = y) -> (@IMAGE _87647 _87658 f (@INTER _87647 s t)) = (@INTER _87658 (@IMAGE _87647 _87658 f s) (@IMAGE _87647 _87658 f t)).
