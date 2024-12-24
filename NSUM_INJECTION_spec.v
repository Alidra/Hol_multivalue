Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7018470 : forall {_129571 : Type'}, forall f : _129571 -> nat, forall p : _129571 -> _129571, forall s : _129571 -> Prop, ((@FINITE _129571 s) /\ ((forall x : _129571, (@IN _129571 x s) -> @IN _129571 (p x) s) /\ (forall x : _129571, forall y : _129571, ((@IN _129571 x s) /\ ((@IN _129571 y s) /\ ((p x) = (p y)))) -> x = y))) -> (@nsum _129571 s (@o _129571 _129571 nat f p)) = (@nsum _129571 s f).
