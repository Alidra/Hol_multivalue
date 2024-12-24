Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7178665 : forall {_135209 : Type'}, forall f : _135209 -> real, forall p : _135209 -> _135209, forall s : _135209 -> Prop, ((@FINITE _135209 s) /\ ((forall x : _135209, (@IN _135209 x s) -> @IN _135209 (p x) s) /\ (forall x : _135209, forall y : _135209, ((@IN _135209 x s) /\ ((@IN _135209 y s) /\ ((p x) = (p y)))) -> x = y))) -> (@sum _135209 s (@o _135209 _135209 real f p)) = (@sum _135209 s f).
