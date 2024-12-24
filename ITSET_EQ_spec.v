Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3839332 : forall {_99546 _99547 : Type'}, forall s : _99546 -> Prop, forall f : _99546 -> _99547 -> _99547, forall g : _99546 -> _99547 -> _99547, forall b : _99547, ((@FINITE _99546 s) /\ ((forall x : _99546, (@IN _99546 x s) -> (f x) = (g x)) /\ ((forall x : _99546, forall y : _99546, forall s' : _99547, (~ (x = y)) -> (f x (f y s')) = (f y (f x s'))) /\ (forall x : _99546, forall y : _99546, forall s' : _99547, (~ (x = y)) -> (g x (g y s')) = (g y (g x s')))))) -> (@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b).
