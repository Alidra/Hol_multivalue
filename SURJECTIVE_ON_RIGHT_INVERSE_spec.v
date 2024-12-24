Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3562737 : forall {_91307 _91308 : Type'} (s : _91307 -> Prop), forall f : _91307 -> _91308, forall t : _91308 -> Prop, (forall y : _91308, (@IN _91308 y t) -> exists x : _91307, (@IN _91307 x s) /\ ((f x) = y)) = (exists g : _91308 -> _91307, forall y : _91308, (@IN _91308 y t) -> (@IN _91307 (g y) s) /\ ((f (g y)) = y)).
