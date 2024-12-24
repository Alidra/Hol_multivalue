Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7124521 : forall {_133152 _133176 : Type'}, forall f : _133176 -> _133152, forall g : _133152 -> real, forall s : _133176 -> Prop, (forall x : _133176, forall y : _133176, ((@IN _133176 x s) /\ ((@IN _133176 y s) /\ ((f x) = (f y)))) -> x = y) -> (@sum _133152 (@IMAGE _133176 _133152 f s) g) = (@sum _133176 s (@o _133176 _133152 real g f)).
