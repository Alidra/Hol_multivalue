Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4019198 : forall {_101850 _101855 : Type'}, forall f : _101855 -> _101850, forall s : _101855 -> Prop, forall n : nat, (forall x : _101855, forall y : _101855, ((@IN _101855 x s) /\ ((@IN _101855 y s) /\ ((f x) = (f y)))) -> x = y) -> (@HAS_SIZE _101850 (@IMAGE _101855 _101850 f s) n) = (@HAS_SIZE _101855 s n).
