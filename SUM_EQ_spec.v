Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7081239 : forall {_132349 : Type'}, forall f : _132349 -> real, forall g : _132349 -> real, forall s : _132349 -> Prop, (forall x : _132349, (@IN _132349 x s) -> (f x) = (g x)) -> (@sum _132349 s f) = (@sum _132349 s g).
