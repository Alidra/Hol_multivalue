Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7071845 : forall {_132081 : Type'}, forall f : _132081 -> real, forall g : _132081 -> real, forall s : _132081 -> Prop, ((@FINITE _132081 s) /\ (forall x : _132081, (@IN _132081 x s) -> real_le (f x) (g x))) -> real_le (@sum _132081 s f) (@sum _132081 s g).
