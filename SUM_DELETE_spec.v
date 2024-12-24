Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7122619 : forall {_132960 : Type'}, forall f : _132960 -> real, forall s : _132960 -> Prop, forall a : _132960, ((@FINITE _132960 s) /\ (@IN _132960 a s)) -> (@sum _132960 (@DELETE _132960 s a) f) = (real_sub (@sum _132960 s f) (f a)).
