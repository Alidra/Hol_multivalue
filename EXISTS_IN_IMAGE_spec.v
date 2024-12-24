Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3388254 : forall {_88003 _88004 : Type'} (P : _88003 -> Prop), forall f : _88004 -> _88003, forall s : _88004 -> Prop, (exists y : _88003, (@IN _88003 y (@IMAGE _88004 _88003 f s)) /\ (P y)) = (exists x : _88004, (@IN _88004 x s) /\ (P (f x))).
