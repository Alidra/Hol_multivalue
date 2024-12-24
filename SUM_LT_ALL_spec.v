Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7077564 : forall {_132203 : Type'}, forall f : _132203 -> real, forall g : _132203 -> real, forall s : _132203 -> Prop, ((@FINITE _132203 s) /\ ((~ (s = (@EMPTY _132203))) /\ (forall x : _132203, (@IN _132203 x s) -> real_lt (f x) (g x)))) -> real_lt (@sum _132203 s f) (@sum _132203 s g).
