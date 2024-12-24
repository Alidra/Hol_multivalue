Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3566182 : forall {_91401 _91404 : Type'}, forall f : _91401 -> _91404, forall s : _91401 -> Prop, (forall x : _91401, forall y : _91401, ((@IN _91401 x s) /\ ((@IN _91401 y s) /\ ((f x) = (f y)))) -> x = y) = (exists g : _91404 -> _91401, forall x : _91401, (@IN _91401 x s) -> (g (f x)) = x).
