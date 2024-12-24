Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4968423 : forall {_113204 : Type'}, forall s : _113204 -> Prop, forall f : _113204 -> _113204, ((@FINITE _113204 s) /\ ((@IMAGE _113204 _113204 f s) = s)) -> forall x : _113204, forall y : _113204, ((@IN _113204 x s) /\ ((@IN _113204 y s) /\ ((f x) = (f y)))) -> x = y.
