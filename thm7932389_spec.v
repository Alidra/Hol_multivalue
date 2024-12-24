Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7932389 : forall {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop), (fun t' : _88266 -> Prop => ((forall y : _88266, (@IN _88266 y t') -> exists x : _88270, (f x) = y) /\ (forall x : _88270, (@IN _88266 (f x) t') = (@IN _88270 x s))) -> (@IMAGE _88270 _88266 f s) = t') t.
