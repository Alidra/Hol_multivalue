Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7123384 : forall {_133013 : Type'}, forall f : _133013 -> real, forall s : _133013 -> Prop, forall a : _133013, (@FINITE _133013 s) -> (@sum _133013 (@DELETE _133013 s a) f) = (@COND real (@IN _133013 a s) (real_sub (@sum _133013 s f) (f a)) (@sum _133013 s f)).
