Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3570865 : forall {_91535 _91536 : Type'}, forall f : _91536 -> _91535, forall s : _91536 -> Prop, forall t : _91535 -> Prop, (forall x : _91536, (@IN _91536 x s) -> @IN _91535 (f x) t) -> ((forall x : _91536, forall y : _91536, ((@IN _91536 x s) /\ ((@IN _91536 y s) /\ ((f x) = (f y)))) -> x = y) /\ (forall y : _91535, (@IN _91535 y t) -> exists x : _91536, (@IN _91536 x s) /\ ((f x) = y))) = (exists g : _91535 -> _91536, (forall y : _91535, (@IN _91535 y t) -> @IN _91536 (g y) s) /\ ((forall y : _91535, (@IN _91535 y t) -> (f (g y)) = y) /\ (forall x : _91536, (@IN _91536 x s) -> (g (f x)) = x))).
