Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3397772 : forall {_88224 _88228 : Type'}, forall f : _88224 -> _88228, forall s : _88224 -> Prop, forall x : _88224, (@IN _88224 x s) -> @IN _88228 (f x) (@IMAGE _88224 _88228 f s).
