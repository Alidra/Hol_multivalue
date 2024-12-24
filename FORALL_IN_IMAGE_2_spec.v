Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3390936 : forall {_88066 _88069 : Type'}, forall f : _88069 -> _88066, forall P : _88066 -> _88066 -> Prop, forall s : _88069 -> Prop, (forall x : _88066, forall y : _88066, ((@IN _88066 x (@IMAGE _88069 _88066 f s)) /\ (@IN _88066 y (@IMAGE _88069 _88066 f s))) -> P x y) = (forall x : _88069, forall y : _88069, ((@IN _88069 x s) /\ (@IN _88069 y s)) -> P (f x) (f y)).
