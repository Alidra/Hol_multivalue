Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7142723 : forall {_133668 : Type'}, forall s : _133668 -> Prop, forall f : _133668 -> real, forall b : real, ((@FINITE _133668 s) /\ ((~ (s = (@EMPTY _133668))) /\ (forall x : _133668, (@IN _133668 x s) -> real_lt (f x) b))) -> real_lt (@sum _133668 s f) (real_mul (real_of_num (@CARD _133668 s)) b).
